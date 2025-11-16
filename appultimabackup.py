# -*- coding: utf-8 -*-
# Dash App: Universal Operations Hub (Scraper, Case Claimer, PDF Extractor, Foodora)

# --- Python Standard Library Imports ---
import io
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile
from urllib.parse import urljoin, urlparse
import traceback
import json
import queue 
import threading 
import logging
from datetime import datetime, timedelta 
import base64 # For dcc.Upload content

# --- Third-Party Library Imports ---
import pandas as pd
import requests
from bs4 import BeautifulSoup
from PIL import Image, UnidentifiedImageError
from selenium import webdriver
from selenium.common.exceptions import (
    ElementClickInterceptedException,
    InvalidSelectorException,
    NoSuchElementException,
    StaleElementReferenceException,
    TimeoutException,
    WebDriverException,
)
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.common.action_chains import ActionChains
import fitz # PyMuPDF

# --- Dash Imports ---
import dash
from dash import dcc, html, Input, Output, State, callback_context, dash_table
# from dash.exceptions import PreventUpdate # May be useful later

# --- Constants ---
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else os.getcwd()
IMAGES_OUTPUT_FOLDER = os.path.join(SCRIPT_DIR, "menu_images_output") 
LOCAL_IMAGES_OUTPUT_FOLDER = os.path.join(SCRIPT_DIR, "local_images_processed") 
PDF_IMAGES_OUTPUT_FOLDER = os.path.join(SCRIPT_DIR, "pdf_images_extracted") 
CASE_LOG_FILE = os.path.join(SCRIPT_DIR, "case_activity_log.xlsx") 

# Case Claimer Constants
APPSHEET_URL = "https://www.appsheet.com/start/3a5110ed-bddf-4499-a905-803ec733f4c6#appName=TaskAllocationAppData-810076412&view=All%20Pending%20Tasks"
USER_DATA_DIR = r"C:\Users\2407850\AppData\Local\Google\Chrome\User Data" 
PROFILE_DIRECTORY = "Default"

# --- Global Variables / Shared State ---
# These are used for simplicity in this transition. For more complex apps,
# consider using dcc.Store more extensively or other state management patterns.
app_log_messages = [] 
data_queue_claimer = queue.Queue() 
stop_event_claimer = threading.Event()
active_portugal_case_store = {} 
active_ghana_case_store = {}
monitoring_active_flag = False 
claimer_status_message = "Idle. Press Start Monitoring." 
claimer_thread_instance = None 

ffmpeg_path_global = None
ffmpeg_path_info_global = "Checking for FFmpeg..."
ffmpeg_version_info_global = ""

# --- Suppress Unwanted Logging ---
loggers_to_silence = ['werkzeug', 'WDM', 'selenium.webdriver.remote.remote_connection', 'selenium.webdriver.common.service']
for logger_name in loggers_to_silence:
    try:
        logging.getLogger(logger_name).setLevel(logging.WARNING) 
    except Exception as e:
        print(f"Debug: Error suppressing logger {logger_name}: {e}")
if 'WDM_LOG' not in os.environ:
    os.environ['WDM_LOG'] = '0'

# --- Logging Helper ---
def add_log(message, level="info"):
    global app_log_messages
    try:
        timestamp = time.strftime("%H:%M:%S"); levels = {"info": "ℹ️ INFO", "warning": "⚠️ WARN", "error": "❌ ERROR", "success": "✅ OK", "debug": "🐞 DEBUG"}
        prefix = levels.get(level, "INFO"); log_entry = f"[{timestamp} {prefix}] {message}"
        app_log_messages.append(log_entry)
        max_log_lines = 300 
        if len(app_log_messages) > max_log_lines:
            app_log_messages = app_log_messages[-max_log_lines:]
        print(log_entry) 
    except Exception as e: print(f"Error in add_log: {e}")

# --- Core Helper Functions ---
def sanitize_filename(name):
    name = str(name) if name is not None else ''; name_part, ext_part = os.path.splitext(name); name = name_part
    name = re.sub(r'[\\/*?:"<>|]', "", name); name = name.replace(" ", "_"); name = re.sub(r'_+', '_', name)
    name = re.sub(r'[^A-Za-z0-9_.-]+', '_', name); name = name[:100].strip('_ ')
    return f"{name}{ext_part.lower()}" if ext_part else name

def find_ffmpeg_on_startup(): 
    global ffmpeg_path_global, ffmpeg_path_info_global, ffmpeg_version_info_global
    if ffmpeg_path_global: return ffmpeg_path_global
    ffmpeg_exe_name = "ffmpeg.exe" if sys.platform == "win32" else "ffmpeg"; found_path = None
    if getattr(sys, 'frozen', False) and hasattr(sys, '_MEIPASS'):
        bundled_path = os.path.join(sys._MEIPASS, ffmpeg_exe_name)
        if os.path.exists(bundled_path): found_path = bundled_path
    if not found_path:
        try:
            script_dir_ff = os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else os.path.dirname(os.path.abspath(sys.argv[0]))
            local_path = os.path.join(script_dir_ff, ffmpeg_exe_name)
            if os.path.exists(local_path): found_path = local_path
        except Exception as e: add_log(f"Debug: Error checking local FFmpeg path: {e}", "debug")
    if not found_path:
        ffmpeg_in_path = shutil.which("ffmpeg")
        if ffmpeg_in_path: found_path = ffmpeg_in_path
    if not found_path:
        add_log("Warning: FFmpeg executable not found at startup.", "warning")
        ffmpeg_path_info_global = "FFmpeg executable not found."; ffmpeg_version_info_global = "Not found."
    else:
        add_log(f"Info: FFmpeg found at {found_path} during startup.", "info"); ffmpeg_path_info_global = f"Found at: `{found_path}`"
        try:
            startupinfo = None; creationflags = 0
            if sys.platform == "win32":
                startupinfo = subprocess.STARTUPINFO(); startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW; startupinfo.wShowWindow = subprocess.SW_HIDE; creationflags = subprocess.CREATE_NO_WINDOW
            verify_process = subprocess.run([found_path, '-version'], capture_output=True, text=True, timeout=5, startupinfo=startupinfo, creationflags=creationflags)
            version_info_line = "Could not verify version."
            if verify_process.returncode == 0 and verify_process.stdout:
                version_info_line = verify_process.stdout.splitlines()[0].strip()
                match = re.search(r'(ffmpeg version.*?)(built.*|$)', version_info_line)
                version_info_line = match.group(1).strip() if match else version_info_line
            ffmpeg_version_info_global = f"`{version_info_line}`"
        except Exception as e: add_log(f"Could not verify FFmpeg version: {e}", "warning"); ffmpeg_version_info_global = "Could not verify version (error)."
    ffmpeg_path_global = found_path
    return found_path 

def convert_image_with_ffmpeg(input_data, ffmpeg_executable_path, output_format='png'):
    if not ffmpeg_executable_path: add_log("DEBUG: FFmpeg Error: No executable path.", "debug"); return None
    temp_input_file = None; process = None
    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".img") as temp_f:
            temp_input_file = temp_f.name; temp_f.write(input_data)
        command = [ffmpeg_executable_path, '-y', '-loglevel', 'error', '-i', temp_input_file, '-f', 'image2pipe', '-vcodec', output_format, 'pipe:1']
        startupinfo = None; creationflags = 0
        if sys.platform == "win32":
            startupinfo = subprocess.STARTUPINFO(); startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW; startupinfo.wShowWindow = subprocess.SW_HIDE; creationflags = subprocess.CREATE_NO_WINDOW
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, startupinfo=startupinfo, creationflags=creationflags)
        stdout, stderr = process.communicate(timeout=15)
        if process.returncode != 0: add_log(f"DEBUG: FFmpeg Error (Code {process.returncode}): {stderr.decode(errors='ignore').strip()}", "debug"); return None
        elif stderr:
            warning_message = stderr.decode(errors='ignore').strip()
            if warning_message and "deprecated pixel format" not in warning_message.lower(): add_log(f"DEBUG: FFmpeg Warning: {warning_message}", "debug")
        if not stdout: add_log(f"DEBUG: FFmpeg Error: No output data", "debug"); return None
        return stdout
    except FileNotFoundError: add_log(f"DEBUG: FFmpeg Error: Executable not found at '{ffmpeg_executable_path}'.", "debug"); return None
    except subprocess.TimeoutExpired:
        add_log("DEBUG: FFmpeg Error: Process timed out.", "debug")
        if process:
            try: process.kill(); process.communicate()
            except Exception as kill_e: add_log(f"DEBUG: Exception during FFmpeg process kill: {kill_e}", "debug")
        return None
    except Exception as e: add_log(f"DEBUG: Error during FFmpeg processing: {e}", "debug"); return None
    finally:
        if temp_input_file and os.path.exists(temp_input_file):
            try: os.remove(temp_input_file)
            except Exception as e_del: add_log(f"DEBUG: Warn - Failed to delete temp file {temp_input_file}: {e_del}", "debug")

def extract_field_data(row_element, column_name, span_sub_xpath="//span[@data-testid='text-type-display-span']", default_value="Not Specified"):
    field_text = default_value
    try:
        if not isinstance(row_element, webdriver.remote.webelement.WebElement):
            add_log(f"DEBUG Extract: Invalid row_element type for '{column_name}'.", "debug"); return default_value
        column_div_xpath = f".//div[@data-testonly-column='{column_name}']"
        column_divs = row_element.find_elements(By.XPATH, column_div_xpath) 
        if not column_divs: return default_value
        column_div = column_divs[0]
        target_elements = column_div.find_elements(By.XPATH, "." + span_sub_xpath)
        if not target_elements: return default_value
        target_element = target_elements[0]
        raw_text = target_element.text
        stripped_text = raw_text.strip() if raw_text else ""
        if stripped_text: field_text = stripped_text
    except NoSuchElementException: pass 
    except StaleElementReferenceException: add_log(f"WARNING Extract StaleElement: Col='{column_name}'. Raising.", "warning"); raise 
    except WebDriverException as e_wd: add_log(f"CRITICAL WebDriver ERROR Extract: Col='{column_name}', WebDriverException: {e_wd}. Raising.", "error"); raise 
    except Exception as e: add_log(f"ERROR Extract (Other type): Col='{column_name}', Exception: {e}. Using default.", "error")
    return field_text

def format_duration(seconds):
    if seconds is None or not isinstance(seconds, (int, float)) or seconds < 0: return "N/A"
    try: return str(timedelta(seconds=int(seconds)))
    except Exception: return "N/A"

LOG_COLUMNS_DEFINITION = ['Date', 'Observed Timestamp', 'Claimed Timestamp', 'Finished Timestamp', 'Duration (seconds)', 'Duration (HH:MM:SS)', 'Case Display ID', 'Country', 'Assigned User', 'Status (Observed)', 'Account Name', 'Case Title', 'Menu Link']

def get_case_log_df():
    try:
        if os.path.exists(CASE_LOG_FILE):
            df = pd.read_excel(CASE_LOG_FILE, engine='openpyxl')
            for col in LOG_COLUMNS_DEFINITION:
                if col not in df.columns: df[col] = pd.NA
            df = df[LOG_COLUMNS_DEFINITION] 
        else:
            df = pd.DataFrame(columns=LOG_COLUMNS_DEFINITION)
            df.to_excel(CASE_LOG_FILE, index=False, engine='openpyxl') 
            add_log(f"Case log file created: {CASE_LOG_FILE}", "info")
        return df
    except Exception as e: 
        add_log(f"Error reading/creating case log file '{CASE_LOG_FILE}': {e}. Returning empty DataFrame.", "error")
        return pd.DataFrame(columns=LOG_COLUMNS_DEFINITION)

def append_to_case_log(log_entry_dict):
    try:
        df_log = get_case_log_df() 
        new_entry_df = pd.DataFrame([log_entry_dict])
        for col in LOG_COLUMNS_DEFINITION: 
            if col not in new_entry_df.columns: new_entry_df[col] = pd.NA
            if col not in df_log.columns: df_log[col] = pd.NA
        new_entry_df = new_entry_df[LOG_COLUMNS_DEFINITION] 
        df_log = df_log[LOG_COLUMNS_DEFINITION] 
        df_log = pd.concat([df_log, new_entry_df], ignore_index=True)
        df_log.to_excel(CASE_LOG_FILE, index=False, engine='openpyxl')
        add_log(f"Case '{log_entry_dict.get('Case Display ID', 'Unknown')}' logged to Excel.", "info")
        return True
    except Exception as e:
        add_log(f"Error appending to case log file '{CASE_LOG_FILE}': {e}", "error")
        traceback.print_exc()
        return False

# (This code starts with setup_scraper_driver and ends after process_extracted_pdf_data)
# (It assumes Part 1, including helper functions like add_log and sanitize_filename, is already in place)

# --- Scraper: Selenium WebDriver Setup ---
def setup_scraper_driver():
    """Sets up Selenium WebDriver for the Scraper (headless)."""
    add_log("Setting up Scraper Chrome WebDriver (headless)...", "info")
    chrome_options = Options()
    chrome_options.add_argument("--headless")
    chrome_options.add_argument("--no-sandbox")
    chrome_options.add_argument("--disable-dev-shm-usage")
    chrome_options.add_argument("--disable-gpu")
    chrome_options.add_argument("--window-size=1920,1080")
    user_agent = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.0.0 Safari/537.36'
    chrome_options.add_argument(f'user-agent={user_agent}')
    chrome_options.add_experimental_option('excludeSwitches', ['enable-logging'])
    chrome_options.add_experimental_option("excludeSwitches", ["enable-automation"])
    chrome_options.add_experimental_option('useAutomationExtension', False)
    chrome_options.add_argument('--disable-blink-features=AutomationControlled')
    
    service_args_selenium = ['--log-level=OFF'] 
    log_output_selenium = os.devnull if sys.platform != "win32" else subprocess.DEVNULL

    try:
        add_log("Installing/Updating ChromeDriver for Scraper...", "info")
        driver_path = ChromeDriverManager().install()
        add_log(f"Scraper ChromeDriver installed/found by webdriver-manager at: {driver_path}", "info")
        service = Service(executable_path=driver_path, log_output=log_output_selenium, service_args=service_args_selenium)
        driver = webdriver.Chrome(service=service, options=chrome_options)
        driver.execute_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined})")
        add_log("Scraper WebDriver setup successful.", "success")
        return driver
    except WebDriverException as wde:
        error_message = f"Scraper WebDriverException: {str(wde)}"
        if "cannot find chrome binary" in str(wde).lower():
            error_message = "Scraper ERROR: Chrome browser executable not found. Please ensure Chrome is installed."
        elif "net::ERR_CONNECTION_REFUSED" in str(wde):
            error_message = "Scraper ERROR: Connection refused during WebDriver setup. Check ChromeDriver port."
        elif "session not created" in str(wde).lower():
            error_message = "Scraper ERROR: Session not created. ChromeDriver/Chrome version mismatch likely. Ensure versions are compatible."
        add_log(error_message, "error")
        raise
    except Exception as e:
        add_log(f"Error setting up Scraper WebDriver: {e}", "error")
        raise

# --- Scraper: Image Processing Function ---
def process_single_image(image_data, output_filename_base, output_folder, ffmpeg_path_to_use): 
    """Processes a single image (bytes). Converts, resizes, and saves as JPEG."""
    global ffmpeg_path_global 
    if not ffmpeg_path_to_use: 
        ffmpeg_path_to_use = ffmpeg_path_global

    if not image_data:
        add_log(f"DEBUG: Skipping {output_filename_base} - No image data provided.", "debug")
        return None
    
    if not os.path.exists(output_folder):
        try:
            os.makedirs(output_folder)
            add_log(f"Created output folder for single image: {output_folder}", "info")
        except Exception as e_mkdir:
            add_log(f"Error creating output folder {output_folder}: {e_mkdir}", "error")
            return None

    output_filepath_jpg = os.path.join(output_folder, f"{output_filename_base}.jpg")

    try:
        img_to_process = None
        needs_ffmpeg_fallback = False
        try:
            img_to_process = Image.open(io.BytesIO(image_data))
        except (IOError, Image.DecompilationBombError, SyntaxError, UnidentifiedImageError) as e:
            add_log(f"DEBUG: PIL failed for {output_filename_base} ({type(e).__name__}: {e}). Attempting FFmpeg fallback.", "debug")
            needs_ffmpeg_fallback = True
        except Exception as e_pil:
            add_log(f"DEBUG: Unexpected PIL error for {output_filename_base}: {type(e_pil).__name__} - {e_pil}", "debug")
            return None

        if needs_ffmpeg_fallback:
            if not ffmpeg_path_to_use:
                add_log(f"DEBUG: PIL failed for {output_filename_base}, FFmpeg needed but not found/configured.", "debug")
                return "FFmpeg required"
            add_log(f"DEBUG: Using FFmpeg for {output_filename_base}...", "debug")
            png_data = convert_image_with_ffmpeg(image_data, ffmpeg_path_to_use) 
            if png_data:
                try:
                    img_to_process = Image.open(io.BytesIO(png_data))
                    add_log(f"DEBUG: FFmpeg fallback successful for {output_filename_base}.", "debug")
                except Exception as e_pil_ffmpeg:
                    add_log(f"DEBUG: Error opening image post-FFmpeg fallback for {output_filename_base}: {e_pil_ffmpeg}", "debug")
                    return None
            else:
                add_log(f"DEBUG: FFmpeg fallback conversion failed for {output_filename_base}.", "debug")
                return None

        if img_to_process:
            try:
                if img_to_process.mode == 'RGBA':
                    bg = Image.new("RGB", img_to_process.size, (255, 255, 255))
                    bg.paste(img_to_process, mask=img_to_process.split()[3])
                    img_final = bg
                elif img_to_process.mode in ('P', 'LA'):
                    img_final = img_to_process.convert('RGB')
                elif img_to_process.mode != 'RGB':
                    add_log(f"DEBUG: Converting image {output_filename_base} from mode {img_to_process.mode} to RGB.", "debug")
                    img_final = img_to_process.convert('RGB')
                else:
                    img_final = img_to_process

                img_resized = img_final.resize((1200, 1200), Image.Resampling.LANCZOS)
                img_resized.save(output_filepath_jpg, "JPEG", quality=90)
                return output_filepath_jpg
            except Exception as e_resize_save:
                add_log(f"DEBUG: Error during resize/save for {output_filename_base}: {e_resize_save}", "debug")
                return None
        else:
            add_log(f"DEBUG: Image load/convert ultimately failed for {output_filename_base}", "debug")
            return None
    except Exception as e_outer:
        add_log(f"DEBUG: Unexpected error processing image {output_filename_base}: {e_outer}", "error")
        return None

# --- Scraper: Main Scraping Logic (ID as Dish Name, Foodora Added, Uber Eats Fix) ---
def scrape_website(target_url, ffmpeg_path_to_use):
    global _internal_item_counter # Used in your Dash app
    _internal_item_counter = 1 # Reset for each scrape_website call

    add_log(f"Scraping: {target_url}", "info")
    parsed_url = urlparse(target_url)
    domain = parsed_url.netloc
    menu_items_data = []
    
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.0.0 Safari/537.36',
        'Accept-Language': 'en-US,en;q=0.9,pt-PT;q=0.8,pt;q=0.7,cs-CZ;q=0.6,cs;q=0.5',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8',
        'Referer': 'https://www.google.com/'
    }

    if 'glovoapp.com' in domain:
        add_log("Glovo: Using Requests/BeautifulSoup...", "info")
        try:
            response = requests.get(target_url, headers=headers, timeout=30)
            response.raise_for_status()
            soup = BeautifulSoup(response.content, 'html.parser')
            menu_containers = soup.select('div.product-row, li[class*=product-list__item], li[class*=product], div[data-testid="product-row"]')
            add_log(f"Glovo: Found {len(menu_containers)} potential containers.", "info")
            current_category = 'Unknown Category'
            for item_element in menu_containers:
                try:
                    category = current_category
                    category_header = item_element.find_previous('p', {'data-test-id': 'list-title', 'class': re.compile(r'\btypography-title-3\b')})
                    if not category_header: category_header = item_element.find_previous(['h2', 'h3', 'h4', 'div[data-testid="category-title"]'])
                    if category_header:
                        cat_text = category_header.get_text(strip=True)
                        if cat_text: category = cat_text; current_category = category
                    
                    name_el = item_element.select_one('[data-testid="product-row-name"], [class*=product-row__name], div[class*="product-card-name"]')
                    name_scraped_original = name_el.get_text(strip=True) if name_el else ''
                    id_for_excel = name_scraped_original if name_scraped_original and name_scraped_original != 'N/A' else f'Glovo_Item_{_internal_item_counter}'

                    desc_el = item_element.select_one('[data-testid="product-row-description"], [class*=product-row__description]')
                    description = desc_el.get_text(strip=True) if desc_el else ''
                    price_el = item_element.select_one('[data-testid*="product-price"], [class*=--price], span[class*="product-price__effective"]')
                    price = 'N/A'
                    if price_el:
                        price_text = price_el.get_text(strip=True); price_cleaned = re.sub(r'[^\d,.]', '', price_text).strip()
                        if ',' in price_cleaned and '.' in price_cleaned: price = price_cleaned.replace(',', '') if price_cleaned.rfind('.') > price_cleaned.rfind(',') else price_cleaned.replace('.', '').replace(',', '.')
                        elif ',' in price_cleaned: price = price_cleaned.replace(',', '.')
                        else: price = price_cleaned
                    
                    img_el = item_element.find('img'); image_url = None
                    if img_el:
                        temp_url = img_el.get('data-src') or img_el.get('srcset') or img_el.get('src')
                        if temp_url:
                            first_url = temp_url.split(',')[0].strip().split(' ')[0]
                            if first_url.startswith('http'): image_url = urljoin(target_url, first_url)
                            if image_url and ('data:image' in image_url or len(image_url) < 20 or 'placeholder' in image_url): image_url = None
                    
                    if name_scraped_original and name_scraped_original != 'N/A' and price != 'N/A':
                        menu_items_data.append({
                            'ID': id_for_excel, 
                            'image_filename': None, 'Category': category, 'Price': price, 
                            'name in pt-PT': name_scraped_original, 'Description in pt-PT': description, 
                            'image_url': image_url
                        })
                    _internal_item_counter += 1
                except Exception as e_item: add_log(f"Glovo: Error processing item approx {_internal_item_counter}: {e_item}", "warning")
        except Exception as e_glovo: add_log(f"Glovo: Scraping failed critically: {e_glovo}", "error"); raise e_glovo

    elif 'ubereats.com' in domain:
        add_log("Uber Eats: Using Selenium (logic from Streamlit app)...", "info")
        driver = None
        try:
            driver = setup_scraper_driver() # Your Dash app's setup_scraper_driver
            if not driver: raise ValueError("WebDriver setup failed for Uber Eats.")

            add_log(f"Uber Eats: Navigating to {target_url}...", "info")
            driver.get(target_url)
            wait = WebDriverWait(driver, 25) 

            try:
                add_log("Uber Eats: Looking for cookie button...", "info")
                accept_xpath = "//button[contains(translate(., 'ABCDEFGHIJKLMNÑOPQRSTUVWXYZ', 'abcdefghijklmnñopqrstuvwxyz'), 'accept') or contains(translate(., 'ABCDEFGHIJKLMNÑOPQRSTUVWXYZ', 'abcdefghijklmnñopqrstuvwxyz'), 'aceitar') or contains(translate(., 'ABCDEFGHIJKLMNÑOPQRSTUVWXYZ', 'abcdefghijklmnñopqrstuvwxyz'), 'agree') or contains(@data-testid, 'accept') or @id='cookie-accept']"
                accept_button = wait.until(EC.element_to_be_clickable((By.XPATH, accept_xpath)))
                driver.execute_script("arguments[0].click();", accept_button) 
                add_log("Uber Eats: Clicked accept button.", "info")
                time.sleep(2.5) 
            except Exception as e_cookie:
                add_log(f"Uber Eats: Cookie button not found/clicked (often OK): {type(e_cookie).__name__}", "debug")

            add_log("Uber Eats: Scrolling page until item count stabilizes (tuned)...", "info")
            SCROLL_PAUSE_TIME = 1.8
            scroll_attempts = 0
            max_scroll_attempts = 200 # From Streamlit
            last_item_count = 0
            no_change_count = 0
            STABILIZATION_CHECKS = 15 # From Streamlit
            container_css_selector = 'li[data-testid^="store-item-"], div[data-testid^="store-item-"], div[role="listitem"]'

            body_element = None
            try:
                body_element = driver.find_element(By.TAG_NAME, 'body')
            except NoSuchElementException:
                add_log("Error: Could not find body element for Uber Eats. Scrolling may fail.", "error")

            while body_element and scroll_attempts < max_scroll_attempts:
                scroll_attempts += 1
                add_log(f"Uber Eats Scroll: Attempt {scroll_attempts}/{max_scroll_attempts}", "debug")
                try:
                    body_element.send_keys(Keys.PAGE_DOWN)
                except Exception as e_keys:
                    add_log(f"Uber Eats Scroll: Error sending Page Down key: {e_keys}", "debug")
                    break 
                time.sleep(SCROLL_PAUSE_TIME)
                time.sleep(0.75) 

                try:
                    current_items = driver.find_elements(By.CSS_SELECTOR, container_css_selector)
                    current_item_count = len(current_items)
                    add_log(f"Uber Eats Scroll: Found {current_item_count} items (previously {last_item_count}).", "debug")
                    if current_item_count == last_item_count:
                        no_change_count += 1
                        add_log(f"Uber Eats Scroll: Item count unchanged ({no_change_count}/{STABILIZATION_CHECKS}).", "debug")
                        if no_change_count >= STABILIZATION_CHECKS:
                            add_log("Uber Eats Scroll: Item count stabilized.", "info")
                            break
                    else:
                        no_change_count = 0 
                    last_item_count = current_item_count
                except Exception as e_find: 
                    add_log(f"Uber Eats Scroll: Error finding items after scroll: {e_find}", "debug")
            
            if scroll_attempts == max_scroll_attempts:
                add_log("Uber Eats Scroll: Max scroll attempts reached.", "warning")
            
            add_log("Uber Eats: Scrolling finished. Waiting for final content...", "info")
            time.sleep(7) 

            add_log(f"Uber Eats: Re-fetching item containers after scroll ('{container_css_selector}')...", "info")
            menu_item_containers = []
            try:
                wait.until(EC.presence_of_element_located((By.CSS_SELECTOR, container_css_selector)))
                menu_item_containers = driver.find_elements(By.CSS_SELECTOR, container_css_selector)
            except Exception as e_final_find:
                add_log(f"Uber Eats: Error finding final containers after scroll: {e_final_find}", "warning")

            num_items_found = len(menu_item_containers)
            add_log(f"Uber Eats: Found {num_items_found} total potential item containers after re-fetch.", "info")

            if num_items_found == 0:
                add_log("Uber Eats ERROR: No item containers found after re-fetch. Scraping will likely fail.", "error")
            
            current_category = 'Unknown Category'
            for item_idx, item_element in enumerate(menu_item_containers):
                item_processed_flag = False 
                try:
                    category = current_category
                    try: # Category extraction from Streamlit code
                        category_xpath = (
                            "./preceding::*[ "
                            "(self::h3[contains(@class, 'mb mc im ik b1')]) or " 
                            "(self::div[@data-testid='catalog-section-title']//h3) or " 
                            "(self::div[contains(@class, 'kf kg ma bb')]//h3) or " 
                            "(self::h2[normalize-space() and not(contains(translate(., 'ABCDEFGHIJKLMNÑOPQRSTUVWXYZ', 'abcdefghijklmnñopqrstuvwxyz'),'featured items'))]) or "
                            "(self::h3[normalize-space() and not(contains(translate(., 'ABCDEFGHIJKLMNÑOPQRSTUVWXYZ', 'abcdefghijklmnñopqrstuvwxyz'),'featured items'))])"
                            "][1]"
                        )
                        category_header = item_element.find_element(By.XPATH, category_xpath)
                        category_text = category_header.text.strip()
                        if category_text and category_text.lower() != 'featured items':
                            category = category_text
                            current_category = category
                    except NoSuchElementException:
                        pass # Keep current_category if new one not found above item
                    except Exception as e_cat_uber: # More general catch for category errors
                         add_log(f"Uber Eats Item {_internal_item_counter}: Error extracting category: {e_cat_uber}", "debug")


                    name = 'N/A'; price = 'N/A'; description = ''; image_url = None
                    price_text_raw_for_desc_check = ''

                    # Name extraction from Streamlit logic
                    try:
                        name_el = item_element.find_element(By.XPATH, "(.//div[not(.//button)]//span[normalize-space() and string-length(normalize-space()) > 3 and not(starts-with(normalize-space(), '€')) and not(starts-with(normalize-space(), '$')) and not(contains(.,'kcal')) and not(contains(translate(.,'0123456789','##########'),'#')) and not(ancestor::button) and not(ancestor::div[contains(@aria-label, 'quantity')]) and not(ancestor::div[contains(@aria-label, 'preço')]) ])[1]")
                        name = name_el.text.strip() if name_el else 'N/A'
                    except NoSuchElementException:
                        try: 
                            name_el = item_element.find_element(By.XPATH, ".//h3[string-length(normalize-space()) > 1 and not(contains(., '€')) and not(contains(., '$')) and not(contains(., 'kcal'))]")
                            name = name_el.text.strip() if name_el else 'N/A'
                        except NoSuchElementException:
                            try:
                                name_el = item_element.find_element(By.XPATH, ".//div[contains(@id, 'title') or contains(@data-testid, 'title') or contains(@style, 'font-weight: 500')][string-length(normalize-space()) > 1 and not(contains(., '€')) and not(contains(., '$')) and not(contains(., 'kcal'))]")
                                name = name_el.text.strip() if name_el else 'N/A'
                            except NoSuchElementException:
                                try: # One more very general attempt from Streamlit
                                    name_el = item_element.find_element(By.XPATH, "(.//span[normalize-space(.)])[1]")
                                    name_candidate = name_el.text.strip()
                                    # Filter out common non-name patterns often caught by too-general selectors
                                    if name_candidate and len(name_candidate) > 2 and not re.match(r'^[\€\$\d.,\s]+kcal$|^[\€\$\d.,\s]+$', name_candidate) and "available" not in name_candidate.lower():
                                        name = name_candidate
                                    else: name = 'N/A'
                                except: name = 'N/A'
                    
                    id_for_excel = name if name and name != 'N/A' else f'UberEats_Item_{_internal_item_counter}'
                    
                    # Price extraction from Streamlit logic
                    try:
                        price_el = item_element.find_element(By.XPATH, "(.//span[contains(., '€') or contains(., '$') or contains(., 'R$') or (contains(., ',') and string-length(substring-after(.,','))=2 and translate(substring-before(.,','),'0123456789','')='') or (contains(., '.') and string-length(substring-after(.,'.'))=2 and translate(substring-before(.,'.'),'0123456789','')='') ])[1]")
                        price_text_raw_for_desc_check = price_el.text.strip()
                        price_text_cleaned = re.sub(r'(?i)\b(from|a partir de)\b\s*', '', price_text_raw_for_desc_check, flags=re.IGNORECASE).strip()
                        price_num_str = re.sub(r'[^\d,.]', '', price_text_cleaned).strip()
                        if ',' in price_num_str and '.' in price_num_str:
                            price = price_num_str.replace('.', '').replace(',', '.') if price_num_str.rfind('.') < price_num_str.rfind(',') else price_num_str.replace(',', '')
                        elif ',' in price_num_str: price = price_num_str.replace(',', '.')
                        elif price_num_str: price = price_num_str
                        else: price = 'N/A'
                    except NoSuchElementException: price = 'N/A'

                    # Description extraction from Streamlit logic
                    try:
                        desc_el = item_element.find_element(By.XPATH, ".//div[contains(@class, 'pv ew')]//span[@class='pw']") # Specific path from Streamlit
                        desc_text = desc_el.text.strip()
                        if desc_text and desc_text.lower() != name.lower() and desc_text != price_text_raw_for_desc_check:
                            description = desc_text
                    except NoSuchElementException:
                        try: 
                            potential_desc_elements = item_element.find_elements(By.XPATH, ".//div[string-length(normalize-space()) > 5 and not(.//h3) and not(contains(., '€')) and not(contains(., '$')) and not(contains(., 'kcal')) and not(ancestor::button)] | .//p[string-length(normalize-space()) > 5 and not(contains(., '€')) and not(contains(., '$')) and not(contains(., 'kcal'))]")
                            for cand_el in potential_desc_elements:
                                desc_text_candidate = cand_el.text.strip()
                                if desc_text_candidate and (not name or (name.lower() not in desc_text_candidate.lower() and desc_text_candidate.lower() not in name.lower())) and desc_text_candidate != price_text_raw_for_desc_check:
                                    description = desc_text_candidate
                                    break 
                        except: description = ''
                    
                    # Image URL extraction from Streamlit logic
                    try:
                        image_url = None
                        try:
                            source_tag = item_element.find_element(By.XPATH, ".//picture/source[@srcset]")
                            srcset = source_tag.get_attribute('srcset')
                            if srcset:
                                sources = [s.strip().split(' ')[0] for s in srcset.split(',') if s.strip() and s.strip().split(' ')[0].startswith('http')]
                                image_url = sources[-1] if sources else None 
                        except NoSuchElementException: pass
                        if not image_url:
                            try:
                                img_tag = item_element.find_element(By.XPATH, ".//picture/img[@src]")
                                image_url = img_tag.get_attribute('src')
                            except NoSuchElementException: pass
                        if not image_url:
                            try:
                                img_tag = item_element.find_element(By.XPATH, ".//img[@src]")
                                image_url = img_tag.get_attribute('src')
                            except NoSuchElementException: pass
                        
                        if image_url and not image_url.startswith(('http:', 'https:')):
                            image_url = urljoin(target_url, image_url)
                        if image_url and ('data:image' in image_url or len(image_url) < 25 or 'placeholder' in image_url.lower() or 'default_image' in image_url.lower()):
                            image_url = None
                    except Exception as e_img_uber: image_url = None


                    if name and name != 'N/A': # Main condition from Streamlit
                        add_log(f"--> Uber Eats Item {_internal_item_counter}: '{name}' | Price: {price} | Category: {category} | Desc: {description[:30]}... | Img: {'Yes' if image_url else 'No'}", "debug")
                        menu_items_data.append({
                            'ID': id_for_excel, 
                            'image_filename': None, 'Category': category, 'Price': price, 
                            'name in pt-PT': name, 
                            'Description in pt-PT': description,
                            'image_url': image_url
                        })
                        _internal_item_counter += 1
                        item_processed_flag = True # Mark as processed
                    
                    # Log if skipped due to missing name (after all attempts)
                    if not item_processed_flag:
                         add_log(f"Uber Eats: Skipping container approx index {item_idx} - name was '{name}'.", "debug")

                except StaleElementReferenceException:
                    add_log(f"Uber Eats: Stale element at index {item_idx}. Skipping.", "warning")
                except Exception as e_item_proc_uber: # More general catch for item processing
                    add_log(f"Uber Eats: Error processing item at index {item_idx}: {e_item_proc_uber}", "warning")
        
        except Exception as e_uber_main: # Catch-all for the main Uber Eats block
            add_log(f"Uber Eats: Scraping failed critically: {e_uber_main}", "error")
            traceback.print_exc()
        finally:
            if driver:
                add_log("Uber Eats: Closing WebDriver...", "info")
                driver.quit()
                add_log("Uber Eats: WebDriver closed.", "info")

    elif 'wolt.com' in domain:
        # ... (Your existing Wolt logic - assuming it's working or will be tuned separately) ...
        add_log("Wolt: Using Selenium...", "info"); driver = None
        try:
            driver = setup_scraper_driver(); 
            if not driver: raise ValueError("WebDriver setup failed for Wolt.")
            add_log(f"Wolt: Navigating to {target_url}...", "info"); driver.get(target_url); wait = WebDriverWait(driver, 20)
            try:
                wolt_accept_xpath = "//button[contains(translate(., 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'accept') or contains(translate(., 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'akceptuj') or contains(translate(., 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'okay') or contains(translate(., 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'got it') or contains(@data-test-id,'Accept') or contains(@data-localization-key, 'banner.accept-button')]"
                accept_button = wait.until(EC.element_to_be_clickable((By.XPATH, wolt_accept_xpath)))
                driver.execute_script("arguments[0].click();", accept_button); add_log("Wolt: Clicked accept button.", "info"); time.sleep(2)
            except Exception as e_cookie_wolt: add_log(f"Wolt: Cookie button not found/clicked (often OK): {type(e_cookie_wolt).__name__}", "debug")
            
            add_log("Wolt: Scrolling page...", "info")
            SCROLL_PAUSE_TIME = 1.8; max_scroll_attempts = 120; last_height = driver.execute_script("return document.body.scrollHeight"); no_change_count = 0; STABILIZATION_CHECKS_WOLT = 8
            body_element = driver.find_element(By.TAG_NAME, 'body')
            for scroll_attempt in range(max_scroll_attempts):
                try: body_element.send_keys(Keys.PAGE_DOWN); time.sleep(SCROLL_PAUSE_TIME)
                except: break
                new_height = driver.execute_script("return document.body.scrollHeight")
                if abs(new_height - last_height) < 50 : no_change_count += 1
                else: no_change_count = 0
                if no_change_count >= STABILIZATION_CHECKS_WOLT: add_log("Wolt: Height stabilized.", "info"); break
                last_height = new_height
            if scroll_attempt == max_scroll_attempts -1: add_log("Wolt: Max scroll attempts reached.", "warning")
            time.sleep(5)
            wolt_container_selector = 'div[data-test-id="horizontal-item-card"], div[data-test-id="VerticalItemCard"], a[data-testid*="venue-product"], div[class*="ProductCardBody"]'
            menu_item_containers = driver.find_elements(By.CSS_SELECTOR, wolt_container_selector)
            add_log(f"Wolt: Found {len(menu_item_containers)} item containers.", "info")
            current_category = 'Unknown Category'

            for item_element in menu_item_containers:
                try:
                    category = current_category
                    try: 
                        category_element = item_element.find_element(By.XPATH, "./preceding::*[self::h1 or self::h2 or self::h3 or @data-test-id='CategoryName' or contains(@class, 'CategoryName__')][1]")
                        cat_text = category_element.text.strip()
                        if cat_text: category = cat_text; current_category = category
                    except NoSuchElementException: pass
                    
                    name_scraped_original = ''; price = 'N/A'; description = ''; image_url = None
                    try: name_el = item_element.find_element(By.CSS_SELECTOR, '[data-test-id="horizontal-item-card-title"], [data-test-id="VerticalItemCardName"], h3, h4, [class*="Title-module"]')
                    except NoSuchElementException: name_el = None
                    if name_el: name_scraped_original = name_el.text.strip()
                    id_for_excel = name_scraped_original if name_scraped_original and name_scraped_original != 'N/A' else f'Wolt_Item_{_internal_item_counter}'
                    
                    try: 
                        price_el = item_element.find_element(By.CSS_SELECTOR, '[data-test-id*="price"], [class*="Price"], [data-hook="item-price"]')
                        price_text_raw = price_el.text.strip(); price_num_str = re.sub(r'[^\d,.]', '', price_text_raw).strip()
                        if ',' in price_num_str and '.' in price_num_str: price = price_num_str.replace('.', '').replace(',', '.') if price_num_str.rfind('.') > price_num_str.rfind(',') else price_num_str.replace(',', '')
                        elif ',' in price_num_str: price = price_num_str.replace(',', '.')
                        elif price_num_str: price = price_num_str
                    except NoSuchElementException: price = 'N/A'
                    
                    try: desc_el = item_element.find_element(By.CSS_SELECTOR, '[data-test-id*="description"], [class*="Description-module"], p[class*="description"]')
                    except NoSuchElementException: desc_el = None
                    if desc_el: description = desc_el.text.strip()
                    
                    try:
                        img_tag = item_element.find_element(By.XPATH, ".//img[(@src and not(contains(@src, 'data:image')) and string-length(@src)>20) or (@srcset and string-length(@srcset)>20)]")
                        srcset = img_tag.get_attribute('srcset'); src = img_tag.get_attribute('src'); temp_url = None
                        if srcset: 
                            sources = [s.strip().split(' ')[0] for s in srcset.split(',') if s.strip() and s.strip().split(' ')[0].startswith('http')]
                            temp_url = sources[-1] if sources else None
                        if not temp_url and src and src.startswith('http'): temp_url = src
                        if temp_url:
                            image_url = urljoin(target_url, temp_url)
                            if 'placeholder' in image_url.lower() or 'default' in image_url.lower() or len(image_url) < 25: image_url = None
                    except NoSuchElementException: image_url = None

                    if name_scraped_original and name_scraped_original != 'N/A' and price != 'N/A':
                        menu_items_data.append({
                            'ID': id_for_excel, 
                            'image_filename': None, 'Category': category, 'Price': price, 
                            'name in pt-PT': name_scraped_original, 
                            'Description in pt-PT': description,
                            'image_url': image_url
                        })
                    _internal_item_counter += 1
                except StaleElementReferenceException: add_log(f"Wolt: Stale element approx {_internal_item_counter}. Skipping.", "warning"); continue
                except Exception as e_item_proc_wolt: add_log(f"Wolt: Error processing item approx {_internal_item_counter}: {e_item_proc_wolt}", "warning")
        except Exception as e_wolt: add_log(f"Wolt: Scraping failed critically: {e_wolt}", "error"); traceback.print_exc(); 
        finally:
            if driver: add_log("Wolt: Closing WebDriver...", "info"); driver.quit()

    elif 'foodora.cz' in domain:
        # ... (Your existing Foodora logic from the Dash app) ...
        add_log("Foodora.cz: Using Selenium...", "info")
        driver = None
        try:
            driver = setup_scraper_driver()
            if not driver: raise ValueError("WebDriver setup failed for Foodora.cz.")
            add_log(f"Foodora.cz: Navigating to {target_url}...", "info"); driver.get(target_url); wait = WebDriverWait(driver, 20)
            try: 
                consent_xpaths = [ "//button[contains(translate(., 'SOUHLASÍM', 'souhlasím'), 'souhlasím')]", "//button[contains(translate(., 'PŘIJMOUT VŠE', 'přijmout vše'), 'přijmout vše')]", "//button[@data-testid='button-acceptAll']", "//button[contains(@class, 'accept') and contains(@class, 'cookie')]" ]
                for xpath_consent in consent_xpaths: 
                    try:
                        consent_button = wait.until(EC.element_to_be_clickable((By.XPATH, xpath_consent)))
                        if consent_button: driver.execute_script("arguments[0].click();", consent_button); add_log("Foodora.cz: Clicked a consent button.", "info"); time.sleep(2); break
                    except TimeoutException: continue
            except Exception as e_cookie_foodora: add_log(f"Foodora.cz: Error handling cookie consent: {e_cookie_foodora}", "warning")

            add_log("Foodora.cz: Scrolling page...", "info") 
            SCROLL_PAUSE_TIME = 2.0; max_scroll_attempts = 60; last_height = driver.execute_script("return document.body.scrollHeight"); no_change_count = 0; STABILIZATION_CHECKS_FOODORA = 5
            body_element = driver.find_element(By.TAG_NAME, 'body')
            for scroll_attempt in range(max_scroll_attempts):
                try: body_element.send_keys(Keys.PAGE_DOWN); time.sleep(SCROLL_PAUSE_TIME)
                except: break
                new_height = driver.execute_script("return document.body.scrollHeight")
                if abs(new_height - last_height) < 100: no_change_count += 1
                else: no_change_count = 0
                if no_change_count >= STABILIZATION_CHECKS_FOODORA: add_log("Foodora.cz: Page scroll height stabilized.", "info"); break
                last_height = new_height
            if scroll_attempt == max_scroll_attempts -1: add_log("Foodora.cz: Max scroll attempts reached.", "warning")
            time.sleep(3)

            category_sections = driver.find_elements(By.CSS_SELECTOR, "div.dish-category-section[data-testid='menu-category-section']")
            add_log(f"Foodora.cz: Found {len(category_sections)} category sections.", "info")
            for section_element in category_sections:
                current_category = "Unknown Category"
                try:
                    category_title_el = section_element.find_element(By.CSS_SELECTOR, "h2.dish-category-title")
                    current_category = category_title_el.text.strip() if category_title_el else "Unknown Category"
                except NoSuchElementException: add_log("Foodora.cz: Category title not found for a section.", "debug")
                
                item_containers = section_element.find_elements(By.CSS_SELECTOR, "li.product-tile[data-testid='menu-product']")
                for item_element in item_containers:
                    try:
                        name_scraped_original = ''; price = 'N/A'; description = ''; image_url = None
                        try:
                            name_el = item_element.find_element(By.CSS_SELECTOR, "span[data-testid='menu-product-name']")
                            name_scraped_original = name_el.text.strip() if name_el else ''
                        except NoSuchElementException: name_scraped_original = ''
                        id_for_excel = name_scraped_original if name_scraped_original else f'Foodora_Item_{_internal_item_counter}'
                        try:
                            price_el = item_element.find_element(By.CSS_SELECTOR, "p[data-testid='menu-product-price']")
                            price_text_raw = price_el.text.strip() if price_el else ''
                            price_match = re.search(r'(\d+([.,]\d{1,2})?)', price_text_raw) 
                            price = price_match.group(1).replace(',', '.') if price_match else 'N/A'
                        except NoSuchElementException: price = 'N/A'
                        try:
                            desc_el = item_element.find_element(By.CSS_SELECTOR, "p.product-tile__description[data-testid='menu-product-description']")
                            description = desc_el.text.strip() if desc_el else ''
                        except NoSuchElementException: description = ''
                        try:
                            img_div = item_element.find_element(By.CSS_SELECTOR, "div.lazy-loaded-dish-photo[data-testid='menu-product-image']")
                            style_attr = img_div.get_attribute("style")
                            url_match = re.search(r'url\("?([^")]*)"?\)', style_attr)
                            if url_match: image_url = url_match.group(1)
                            if image_url and ('data:image' in image_url or len(image_url) < 20): image_url = None
                        except NoSuchElementException: image_url = None
                        if name_scraped_original and price != 'N/A':
                            menu_items_data.append({'ID': id_for_excel, 'image_filename': None, 'Category': current_category, 'Price': price, 'name in pt-PT': name_scraped_original, 'Description in pt-PT': description, 'image_url': image_url})
                        _internal_item_counter += 1
                    except Exception as e_item_foodora: add_log(f"Foodora.cz: Error processing item in '{current_category}': {e_item_foodora}", "warning")
        except Exception as e_foodora: add_log(f"Foodora.cz: Scraping failed critically: {e_foodora}", "error"); traceback.print_exc();
        finally:
            if driver: add_log("Foodora.cz: Closing WebDriver...", "info"); driver.quit()
    
    else: 
        add_log(f"Domain '{domain}' not specifically handled. Using generic Requests/BS4.", "warning")
        try:
            response = requests.get(target_url, headers=headers, timeout=25); response.raise_for_status()
            soup = BeautifulSoup(response.content, 'html.parser'); add_log("Generic scrape attempt...", "info")
            generic_selectors = ['div.menu-item', 'li.product', 'article.dish', '.item-card', 'div[class*="item"]', 'div[class*="product"]']
            menu_item_containers = []
            for selector in generic_selectors:
                menu_item_containers = soup.select(selector)
                if menu_item_containers: add_log(f"Found items using generic selector: '{selector}'", "info"); break
            if not menu_item_containers: add_log("Generic: Could not find elements.", "warning")
            for item_element in menu_item_containers:
                try:
                    name_el = item_element.select_one('.item-name, .product-name, .title, h3, h4, [class*="name"]')
                    name_scraped_original = name_el.text.strip() if name_el else ''
                    id_for_excel = name_scraped_original if name_scraped_original and name_scraped_original != 'N/A' else f'Generic_Item_{_internal_item_counter}'
                    price_el = item_element.select_one('.item-price, .product-price, .price, [class*="price"]')
                    price = price_el.text.strip() if price_el else 'N/A' 
                    desc_el = item_element.select_one('.item-description, .product-description, .description, p, [class*="desc"]')
                    description = desc_el.text.strip() if desc_el else ''
                    category = 'Generic Fallback'; image_tag = item_element.find('img'); image_url = None
                    if image_tag:
                        temp_url = image_tag.get('data-src') or image_tag.get('src')
                        if temp_url:
                            abs_url = urljoin(target_url, temp_url)
                            if abs_url.startswith('http') and 'data:image' not in abs_url and len(abs_url) > 20: image_url = abs_url
                    if name_scraped_original and name_scraped_original != 'N/A' and price != 'N/A':
                        menu_items_data.append({'ID': id_for_excel, 'image_filename': None, 'Category': category, 'Price': price, 'name in pt-PT': name_scraped_original, 'Description in pt-PT': description, 'image_url': image_url})
                    _internal_item_counter +=1
                except Exception as e_gen_item: add_log(f"Generic: Error processing item: {e_gen_item}", "warning")
        except requests.exceptions.RequestException as e_req_gen: add_log(f"Error fetching generic URL: {e_req_gen}", "error"); raise e_req_gen
        except Exception as e_gen_other: add_log(f"Error during generic scraping: {e_gen_other}", "error"); raise e_gen_other

    if not menu_items_data:
        add_log(f"Warning: No menu items were successfully scraped from {target_url}", "warning")
        
    return menu_items_data

# --- Scraper: Data and Image Processing after Scraping ---
def process_web_images_and_data(menu_items_data, base_url, ffmpeg_path_to_use): 
    global ffmpeg_path_global
    if not ffmpeg_path_to_use: ffmpeg_path_to_use = ffmpeg_path_global

    if not os.path.exists(IMAGES_OUTPUT_FOLDER):
        try: os.makedirs(IMAGES_OUTPUT_FOLDER)
        except Exception as e: add_log(f"Error creating web image output folder: {e}", "error"); return pd.DataFrame(), []
    processed_image_files = []; df = pd.DataFrame(); headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.0.0 Safari/537.36', 'Referer': base_url}
    if not menu_items_data: return df, processed_image_files
    try:
        df = pd.DataFrame(menu_items_data)
        cols_needed = ['ID', 'image_filename', 'Category', 'Price', 'name in pt-PT', 'Description in pt-PT', 'image_url']
        for col in cols_needed:
            if col not in df.columns: 
                df[col] = pd.NA 
        add_log(f"Processing Web Images: DataFrame created ({df.shape}). Columns: {df.columns.tolist()}", "info")
        total_items = len(df)
        
        for index, row in df.iterrows():
            add_log(f"Processing web image {index+1}/{total_items}", "debug") 
            dish_name_for_file = str(row.get('ID', f'item_unnamed_{index}')) 
            sanitized_base_name = sanitize_filename(f"{index}_{dish_name_for_file}")
            image_url_val = row.get('image_url')
            df.loc[index, 'image_filename'] = 'Processing Error' 
            if not image_url_val or not isinstance(image_url_val, str) or not image_url_val.startswith(('http:', 'https:')):
                df.loc[index, 'image_filename'] = 'No valid URL'; continue
            if not sanitized_base_name: 
                df.loc[index, 'image_filename'] = 'Invalid name for file'; continue
            try:
                img_response = requests.get(image_url_val, headers=headers, timeout=20, stream=True); img_response.raise_for_status()
                content_type = img_response.headers.get('Content-Type', '').lower()
                is_image = content_type.startswith('image/') or any(str(image_url_val).lower().endswith(ext) for ext in ['.jpg', '.jpeg', '.png', '.gif', '.webp', '.avif', '.tiff', '.bmp'])
                if not is_image: df.loc[index, 'image_filename'] = f'Non-image ({content_type[:20]})'; continue
                image_data_bytes = img_response.content
                if not image_data_bytes: df.loc[index, 'image_filename'] = 'DL empty file'; continue
                output_filepath = process_single_image(image_data_bytes, sanitized_base_name, IMAGES_OUTPUT_FOLDER, ffmpeg_path_to_use)
                if output_filepath == "FFmpeg required": current_image_status = "FFmpeg required"
                elif output_filepath: current_image_status = os.path.basename(output_filepath); processed_image_files.append(output_filepath)
                else: current_image_status = 'Image processing failed'
                df.loc[index, 'image_filename'] = current_image_status
            except requests.exceptions.Timeout: df.loc[index, 'image_filename'] = 'DL Timeout'
            except requests.exceptions.HTTPError as e_http: df.loc[index, 'image_filename'] = f'DL HTTP Err {e_http.response.status_code}'
            except requests.exceptions.RequestException: df.loc[index, 'image_filename'] = f'DL Conn Err'
            except Exception as e_unexp: add_log(f"Web Img DL for '{dish_name_for_file}': Unexp err: {e_unexp}", "error"); df.loc[index, 'image_filename'] = 'Unknown Proc Error'
    except Exception as e_proc_web: 
        add_log(f"CRITICAL WEB IMAGE PROCESSING ERROR: {e_proc_web}", "error"); traceback.print_exc()
        return df if 'df' in locals() and isinstance(df, pd.DataFrame) else pd.DataFrame(), processed_image_files
    return df, processed_image_files

# --- Scraper: Output File Generation (Updated for Conditional Columns) ---
def create_output_files(df, processed_image_files, images_folder_path, selected_country):
    excel_filename_base = f"scraped_menu_{selected_country.lower()}"
    final_excel_filename = f"{excel_filename_base}_final.xlsx"
    zip_filename = f"scraped_menu_images_{selected_country.lower()}.zip"
    excel_data = None; zip_data = None
    if df is not None and not df.empty:
        final_df_for_excel = pd.DataFrame()
        if selected_country == "Portugal":
            desired_excel_column_order = ['ID', 'images', 'category', 'price', 'name pt', 'name en', 'description pt', 'description en']
            final_df_for_excel['ID'] = df['ID']; final_df_for_excel['images'] = df.get('image_filename', pd.NA)
            final_df_for_excel['category'] = df.get('Category', pd.NA); final_df_for_excel['price'] = df.get('Price', pd.NA)
            final_df_for_excel['name pt'] = df['name in pt-PT']; final_df_for_excel['name en'] = pd.NA 
            final_df_for_excel['description pt'] = df.get('Description in pt-PT', pd.NA); final_df_for_excel['description en'] = pd.NA
        elif selected_country == "Ghana" or selected_country == "Czechia": 
            desired_excel_column_order = ['ID', 'Category', 'Images', 'Name en-US', 'Description en-US', 'Price']
            final_df_for_excel['ID'] = df['ID']; final_df_for_excel['Category'] = df.get('Category', pd.NA)
            final_df_for_excel['Images'] = df.get('image_filename', pd.NA); final_df_for_excel['Name en-US'] = df['name in pt-PT'] 
            final_df_for_excel['Description en-US'] = df.get('Description in pt-PT', pd.NA); final_df_for_excel['Price'] = df.get('Price', pd.NA)
        else: 
            add_log(f"Warning: Unknown country '{selected_country}' for Excel. Using default PT structure.", "warning")
            desired_excel_column_order = ['ID', 'images', 'category', 'price', 'name pt', 'description pt'] 
            final_df_for_excel['ID'] = df['ID']; final_df_for_excel['images'] = df.get('image_filename', pd.NA)
            final_df_for_excel['category'] = df.get('Category', pd.NA); final_df_for_excel['price'] = df.get('Price', pd.NA)
            final_df_for_excel['name pt'] = df['name in pt-PT']; final_df_for_excel['description pt'] = df.get('Description in pt-PT', pd.NA)
        final_df_for_excel = final_df_for_excel.reindex(columns=desired_excel_column_order)
        try:
            excel_buffer = io.BytesIO()
            with pd.ExcelWriter(excel_buffer, engine='openpyxl') as writer: final_df_for_excel.to_excel(writer, index=False, sheet_name=f'Menu_{selected_country}')
            excel_data = excel_buffer.getvalue(); add_log(f"Excel data for {selected_country} created ({len(excel_data)} bytes).", "info")
        except Exception as e_excel: add_log(f"Error creating Excel for {selected_country}: {e_excel}", "error"); traceback.print_exc()
    else: add_log(f"DataFrame empty, skipping Excel for {selected_country} scrape.", "warning")
    if processed_image_files:
        existing_files_on_disk = [f for f in processed_image_files if os.path.exists(f) and os.path.isfile(f)]
        if existing_files_on_disk:
            try:
                zip_buffer = io.BytesIO()
                with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
                    add_log(f"Zipping {len(existing_files_on_disk)} web images for {selected_country}...", "info")
                    for file_path in existing_files_on_disk: zipf.write(file_path, arcname=os.path.basename(file_path))
                zip_data = zip_buffer.getvalue(); add_log(f"Web images ZIP data for {selected_country} created ({len(zip_data)} bytes).", "info")
            except Exception as e_zip: add_log(f"Error creating web images zip for {selected_country}: {e_zip}", "error")
        else: add_log(f"No processed web image files on disk for {selected_country} zipping.", "warning")
    else: add_log(f"No web images listed as processed for {selected_country} zipping.", "warning")
    return excel_data, final_excel_filename, zip_data, zip_filename

# --- Helper Function for Auto-Scraping Claimed Case Links ---
def scrape_and_prepare_case_files(url_to_scrape, case_country, case_id_for_log=""):
    global ffmpeg_path_global 
    if not url_to_scrape or not isinstance(url_to_scrape, str) or not url_to_scrape.startswith('http'):
        add_log(f"Auto-Scrape: Invalid URL for case '{case_id_for_log}': {url_to_scrape}", "warning"); return None
    add_log(f"Auto-Scrape: Starting for case '{case_id_for_log}', URL: {url_to_scrape}, Country: {case_country}", "info")
    
    if not ffmpeg_path_global: 
        add_log("Auto-Scrape: FFmpeg path not set globally. Attempting to find now.", "warning")
        find_ffmpeg_on_startup() 
    
    class DummyProgressArea: 
        def empty(self): return self
        def progress(self, val): pass
        def text(self, txt): pass
    dummy_log_area = DummyProgressArea()

    try:
        menu_data = scrape_website(url_to_scrape, ffmpeg_path_global) 
        if not menu_data: add_log(f"Auto-Scrape: No data from scraping URL for case '{case_id_for_log}'.", "warning"); return None
        
        df_processed, images_saved = process_web_images_and_data(
            menu_data, url_to_scrape, ffmpeg_path_global
        )

        if df_processed is None or df_processed.empty: add_log(f"Auto-Scrape: DataFrame empty after processing for case '{case_id_for_log}'.", "warning"); return None

        excel_bytes, excel_name, zip_bytes, zip_name = create_output_files(
            df_processed, images_saved, IMAGES_OUTPUT_FOLDER, case_country
        )
        
        if excel_bytes or zip_bytes:
            add_log(f"Auto-Scrape: Files prepared for case '{case_id_for_log}'. Excel: {'Yes' if excel_bytes else 'No'}, ZIP: {'Yes' if zip_bytes else 'No'}", "info")
            return {"excel_bytes": excel_bytes, "excel_name": excel_name, "zip_bytes": zip_bytes, "zip_name": zip_name}
        else: add_log(f"Auto-Scrape: No output files (Excel/ZIP) generated for case '{case_id_for_log}'.", "warning"); return None
    except Exception as e: add_log(f"Auto-Scrape: CRITICAL ERROR for case '{case_id_for_log}', URL '{url_to_scrape}': {e}", "error"); traceback.print_exc(); return None

# --- PDF Processing Functions ---
def extract_text_and_images_from_pdf(pdf_file_bytes, pdf_name):
    """Extracts text blocks and images from a PDF file."""
    global ffmpeg_path_global 
    extracted_items = []
    extracted_images_paths = []
    doc = None
    _internal_pdf_item_counter = 1 

    try:
        doc = fitz.open(stream=pdf_file_bytes, filetype="pdf")
        add_log(f"PDF '{pdf_name}': Opened with {doc.page_count} pages.", "info")

        for page_num in range(len(doc)):
            page = doc.load_page(page_num)
            
            blocks = page.get_text("blocks") 
            for i, block in enumerate(blocks):
                if block[6] == 0: 
                    text = block[4].replace("\n", " ").strip()
                    text = re.sub(r'\s+', ' ', text) 
                    if len(text) > 5: 
                        lines = block[4].strip().split('\n')
                        item_name_scraped = lines[0].strip()
                        item_desc = " ".join(lines[1:]).strip() if len(lines) > 1 else ""
                        
                        id_for_excel = item_name_scraped if item_name_scraped else f"PDF_{sanitize_filename(pdf_name)}_Item_{_internal_pdf_item_counter}"

                        price_match = re.search(r'(\€|\$|R\$|£|zł|GHS)?\s*(\d+([.,]\d{1,2})?)', text, re.IGNORECASE) 
                        item_price = price_match.group(0).strip() if price_match else "N/A"
                        if price_match and item_name_scraped.endswith(item_price): item_name_scraped = item_name_scraped[:-len(item_price)].strip()
                        if price_match and item_desc.startswith(item_price): item_desc = item_desc[len(item_price):].strip()

                        extracted_items.append({
                            "ID": id_for_excel, 
                            "name in pt-PT": item_name_scraped, 
                            "Description in pt-PT": item_desc, 
                            "Price": item_price,
                            "Category": "PDF Extracted", 
                            "image_url": None, 
                            "image_filename": None 
                        })
                        _internal_pdf_item_counter +=1
            
            image_list = page.get_images(full=True)
            for img_index, img in enumerate(image_list):
                xref = img[0]
                try:
                    base_image = doc.extract_image(xref)
                    if not base_image: continue 
                    image_bytes = base_image["image"]
                except Exception as e_img_extract:
                    add_log(f"PDF '{pdf_name}': Error extracting image xref {xref} on page {page_num + 1}: {e_img_extract}", "warning")
                    continue

                sanitized_pdf_name = sanitize_filename(os.path.splitext(pdf_name)[0])
                img_filename_base = f"pdf_{sanitized_pdf_name}_p{page_num + 1}_img{img_index}"
                
                if not os.path.exists(PDF_IMAGES_OUTPUT_FOLDER):
                    os.makedirs(PDF_IMAGES_OUTPUT_FOLDER)
                
                processed_image_path = process_single_image(image_bytes, img_filename_base, PDF_IMAGES_OUTPUT_FOLDER, ffmpeg_path_global)
                
                if processed_image_path:
                    extracted_images_paths.append(processed_image_path)
                    if not any(item.get("image_filename") == os.path.basename(processed_image_path) for item in extracted_items):
                        extracted_items.append({
                            "ID": f"PDF_Image_{_internal_pdf_item_counter}", 
                            "name in pt-PT": f"Image: {os.path.basename(processed_image_path)}",
                            "Description in pt-PT": f"Extracted from page {page_num + 1} of {pdf_name}",
                            "Price": "N/A", "Category": "PDF Image", "image_url": None,
                            "image_filename": os.path.basename(processed_image_path)
                        })
                        _internal_pdf_item_counter +=1
        add_log(f"PDF '{pdf_name}': Extracted {len(extracted_items)} items (text/image placeholders) and processed {len(extracted_images_paths)} images.", "info")
    except Exception as e: add_log(f"Error processing PDF '{pdf_name}': {e}", "error"); traceback.print_exc()
    finally:
        if doc: doc.close()
    return extracted_items, extracted_images_paths

def process_extracted_pdf_data(uploaded_pdf_files, selected_country_pdf): 
    """Processes multiple uploaded PDF files and prepares data for Excel/ZIP."""
    all_pdf_items_data = []
    all_pdf_image_paths = []
    if not uploaded_pdf_files: add_log("No PDF files uploaded for processing.", "warning"); return pd.DataFrame(), []
    total_files = len(uploaded_pdf_files)
    
    for i, uploaded_file in enumerate(uploaded_pdf_files):
        pdf_name = uploaded_file.name
        add_log(f"[PDF] Processing {i+1}/{total_files}: {pdf_name}", "info") 
        pdf_bytes = uploaded_file.getvalue()
        items, image_paths = extract_text_and_images_from_pdf(pdf_bytes, pdf_name)
        all_pdf_items_data.extend(items); all_pdf_image_paths.extend(image_paths) 
        
    add_log("PDF processing finished.", "info") 

    if not all_pdf_items_data: add_log("No items extracted from any PDF.", "warning"); return pd.DataFrame(), []
    df_pdf_processed = pd.DataFrame(all_pdf_items_data)
    cols_needed = ['ID', 'image_filename', 'Category', 'Price', 'name in pt-PT', 'Description in pt-PT', 'image_url']
    for col in cols_needed:
        if col not in df_pdf_processed.columns: df_pdf_processed[col] = pd.NA
    return df_pdf_processed, all_pdf_image_paths

# (This code starts with initialize_claimer_driver and ends after run_claimer_loop)
# (It assumes Part 1 and Part 2, including all helper functions, scraper logic with Foodora,
#  PDF processing functions, and scrape_and_prepare_case_files, are already in place above this block.)

# --- Case Claimer: Selenium WebDriver Setup ---
def initialize_claimer_driver():
    """Initializes Selenium WebDriver for the Case Claimer with User Profile."""
    global claimer_status_message # Declare intent to modify global
    add_log(f"Claimer: Initializing WebDriver with USER_DATA_DIR = '{USER_DATA_DIR}'", "info")
    if not USER_DATA_DIR or not os.path.isdir(USER_DATA_DIR):
        claimer_status_message = f"Error: USER_DATA_DIR ('{USER_DATA_DIR}') is invalid or not found."
        add_log(claimer_status_message, "error")
        return None
    
    options = webdriver.ChromeOptions()
    options.add_argument(f"--user-data-dir={USER_DATA_DIR}")
    options.add_argument(f"--profile-directory={PROFILE_DIRECTORY}")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--start-maximized")
    options.add_argument("--disable-extensions") 
    options.add_experimental_option("excludeSwitches", ["enable-automation", "enable-logging"])
    options.add_experimental_option('useAutomationExtension', False)
    options.add_argument('--disable-blink-features=AutomationControlled')
    options.add_argument('--disable-infobars')
    options.add_argument('--disable-popup-blocking')
    options.add_argument('--ignore-certificate-errors')
    
    service_args_selenium = ['--log-level=OFF'] 
    log_output_selenium = os.devnull if sys.platform != "win32" else subprocess.DEVNULL

    add_log(f"Claimer: Attempting launch with profile: {USER_DATA_DIR}/{PROFILE_DIRECTORY}", "info")
    add_log("!!! ENSURE CHROME IS COMPLETELY CLOSED BEFORE STARTING CLAIMER !!!", "warning")
    
    try:
        driver_path = ChromeDriverManager().install() 
        add_log(f"Claimer ChromeDriver installed/found by webdriver-manager at: {driver_path}", "info")
        service = Service(executable_path=driver_path, log_output=log_output_selenium, service_args=service_args_selenium)
        driver = webdriver.Chrome(service=service, options=options)
        driver.execute_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined})")
        add_log("Claimer WebDriver initialized.", "success")
        time.sleep(3) 
        return driver
    except WebDriverException as e_wd_init:
        claimer_status_message = "Claimer WebDriver Initialization FAILED. Check logs."
        add_log(f"FATAL Claimer WebDriver Initialization Error: {e_wd_init}", "error")
        return None
    except Exception as e:
        claimer_status_message = "Claimer WebDriver Error (Other). Check logs."
        add_log(f"ERROR initializing Claimer WebDriver (Non-WebDriverException): {e}", "error")
        return None

# --- Case Claimer: Login Status Check ---
def check_claimer_login_status(driver):
    """Checks if the user is logged into AppSheet."""
    global claimer_status_message # Declare intent to modify global
    add_log("Claimer: Checking login status...", "info")
    if driver is None: return False
    try: _ = driver.current_url 
    except WebDriverException as e_wd_responsive:
        claimer_status_message = "Claimer Login Check Failed (WebDriver Unresponsive)."
        add_log(f"Claimer CRITICAL: WebDriver not responsive: {e_wd_responsive}", "error")
        return False

    page_load_timeout_seconds = 120 
    try: driver.set_page_load_timeout(page_load_timeout_seconds)
    except Exception as e_timeout_set: add_log(f"Claimer WARNING: Could not set page load timeout: {e_timeout_set}", "warning")

    add_log(f"Claimer: Navigating to AppSheet URL: {APPSHEET_URL}", "info")
    try:
        driver.get(APPSHEET_URL)
        add_log("Claimer: Initial navigation to AppSheet URL complete. Waiting for page body (10s)...", "debug")
        WebDriverWait(driver, 10).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        
        add_log("Claimer: Page body present. Waiting for AppSheet to potentially settle (additional 10s sleep)...", "debug")
        time.sleep(10)

        current_url_after_get = driver.current_url
        add_log(f"Claimer: Current URL after get and sleep: {current_url_after_get}", "debug")

        if "appsheet.com" not in current_url_after_get.lower():
            claimer_status_message = f"Claimer: Redirected to unexpected URL: {current_url_after_get}. Login likely failed."
            add_log(claimer_status_message, "error")
            return False

        wait_for_app_element_timeout = 90 
        app_loaded_indicator_xpath = "//div[@data-testid='appname-and-viewname'] | //div[@title='All Pending Tasks'] | //div[contains(@class,'appsheet-container') and .//div[@role='table']]"
        
        add_log(f"Claimer: Attempting to find a reliable app loaded indicator (up to {wait_for_app_element_timeout}s)... XPath: {app_loaded_indicator_xpath}", "debug")
        WebDriverWait(driver, wait_for_app_element_timeout).until(
            EC.visibility_of_element_located((By.XPATH, app_loaded_indicator_xpath))
        )
        add_log("Claimer: Reliable app loaded indicator found and visible.", "debug")
        
        add_log("Claimer: Basic login check passed.", "success")
        return True
        
    except TimeoutException as te:
        page_source_filename = f"appsheet_timeout_debug_{time.strftime('%Y%m%d_%H%M%S')}.html"
        try:
            with open(page_source_filename, "w", encoding="utf-8") as f: f.write(driver.page_source)
            add_log(f"Claimer: TimeoutException during login status check. Page source saved to {page_source_filename}", "error")
        except Exception as e_save: add_log(f"Claimer: TimeoutException during login, and also failed to save page source: {e_save}", "error")
        claimer_status_message = "Claimer Login Check Failed (Timeout waiting for critical page elements after navigation)."
        add_log(f"Claimer ERROR (Timeout after navigation, waiting for app elements): {te}", "error") 
        return False
    except WebDriverException as e_wd_login:
        claimer_status_message = "Claimer Login Check Failed (WebDriver Error during navigation/element search)."
        add_log(f"Claimer CRITICAL WebDriver ERROR: {e_wd_login}", "error") 
        return False
    except Exception as e_login:
        claimer_status_message = "Claimer Login Check Failed (Other Error)."
        add_log(f"Claimer ERROR (Other): {e_login}", "error") 
        return False
    finally:
        try: driver.set_page_load_timeout(30) 
        except: pass

# --- Case Claimer: Core Scraper Logic (Updated for Auto-Scraping and Colleague Logging) ---
def find_and_claim_cases(driver, data_q: queue.Queue, stop_event: threading.Event):
    global active_portugal_case_store, active_ghana_case_store, ffmpeg_path_global

    if driver is None:
        add_log("Claimer CRITICAL: find_and_claim_cases called with driver=None.", "error")
        data_q.put_nowait({"status": "DRIVER_DEAD_PRE_CHECK", "claimed_case_data": None})
        return "DRIVER_DEAD_PRE_CHECK"

    claimed_case_details_to_return = None
    current_pass_status = "OK_NO_NEW_CLAIMABLE_SLOT_OR_CASE"
    wait = WebDriverWait(driver, 30)
    detail_page_wait = WebDriverWait(driver, 30)

    active_pt_case_exists = bool(active_portugal_case_store)
    active_gh_case_exists = bool(active_ghana_case_store)

    if active_pt_case_exists and active_gh_case_exists:
        add_log("Claimer DEBUG: Both Portugal and Ghana slots are full. Skipping claim attempts for this cycle.", "debug")
        return "OK_BOTH_SLOTS_FULL"

    try:
        try:
            current_url_before_row_find = driver.current_url
            add_log(f"Claimer DEBUG: Responsive. Current URL before finding rows: {current_url_before_row_find}", "debug")
        except WebDriverException as e_resp:
            add_log(f"Claimer CRITICAL: WebDriver unresponsive at start of find_and_claim (before row find): {e_resp}", "error")
            traceback.print_exc()
            current_pass_status = "DRIVER_DEAD_RESP_CHECK"
            return current_pass_status

        all_rows_list = []
        if current_pass_status not in ["DRIVER_DEAD", "STOPPED", "DRIVER_DEAD_RESP_CHECK"]:
            all_rows_xpath = "//span[@data-testid='table-view-row' and contains(@class, 'TableViewRow')]"
            try:
                add_log(f"Claimer: Actively waiting up to {wait._timeout}s for rows with XPath: {all_rows_xpath}", "debug")
                time.sleep(3)

                WebDriverWait(driver, wait._timeout).until(
                    EC.presence_of_all_elements_located((By.XPATH, all_rows_xpath))
                )
                time.sleep(2)
                all_rows_list = driver.find_elements(By.XPATH, all_rows_xpath)

                if not all_rows_list:
                    add_log("Claimer INFO: No rows found on page after explicit wait. (AppSheet view might be empty, filtered, or not fully loaded).", "info")
                    current_pass_status = "OK_NO_ROWS_VISIBLE"
                else:
                    add_log(f"Claimer DEBUG: Found {len(all_rows_list)} candidate row elements after wait.", "debug")
            except TimeoutException:
                add_log("Claimer INFO: Timeout waiting for any rows to appear. Page might be empty, not fully loaded, or navigation issue.", "info")
                page_source_filename = f"appsheet_timeout_rows_debug_{time.strftime('%Y%m%d_%H%M%S')}.html"
                try:
                    with open(page_source_filename, "w", encoding="utf-8") as f: f.write(driver.page_source)
                    add_log(f"Claimer: Page source saved to {page_source_filename} on row TimeoutException.", "info")
                except Exception as e_save_rows_timeout: add_log(f"Claimer: Failed to save page source on row TimeoutException: {e_save_rows_timeout}", "error")
                current_pass_status = "OK_TIMEOUT_NO_ROWS"
            except WebDriverException as e_wd_rows:
                add_log(f"Claimer CRITICAL: WebDriverException while finding rows: {e_wd_rows}", "error")
                traceback.print_exc()
                current_pass_status = "DRIVER_DEAD_ROW_FIND"
                return current_pass_status
            except Exception as e_rows_other:
                add_log(f"Claimer CRITICAL: Other unexpected error during row finding phase: {e_rows_other}", "error")
                traceback.print_exc()
                current_pass_status = "ERROR_UNEXPECTED_FINDING_ROWS"
                return current_pass_status

        possible_early_exit_statuses = [
            "DRIVER_DEAD", "STOPPED", "OK_NO_ROWS_VISIBLE", "OK_TIMEOUT_NO_ROWS",
            "DRIVER_DEAD_RESP_CHECK", "DRIVER_DEAD_ROW_FIND", "ERROR_UNEXPECTED_FINDING_ROWS"
        ]

        if current_pass_status not in possible_early_exit_statuses and all_rows_list:
            add_log(f"Claimer INFO: Starting to scan {len(all_rows_list)} found rows for details.", "info")
            for i in range(len(all_rows_list)):
                if stop_event.is_set():
                    add_log("Claimer DEBUG: Stop event detected during row processing loop.", "debug")
                    current_pass_status = "STOPPED"; break

                row_element_to_process = None
                display_id_for_log_temp = f"Row_Index_{i+1}"

                try:
                    current_row_xpath = f"({all_rows_xpath})[{i+1}]"
                    add_log(f"Claimer DEBUG: Attempting to locate row with XPath: {current_row_xpath}", "debug")
                    row_element_to_process = WebDriverWait(driver, 7).until(
                        EC.presence_of_element_located((By.XPATH, current_row_xpath))
                    )

                    add_log(f"Claimer DEBUG: Attempting to scroll and check visibility for Row Element ID: {row_element_to_process.id}", "debug")
                    is_row_visible_and_interactable = False
                    for attempt in range(2):
                        try:
                            driver.execute_script("arguments[0].scrollIntoView({behavior: 'auto', block: 'center', inline: 'nearest'});", row_element_to_process)
                            time.sleep(0.75 + (attempt * 0.5))

                            if row_element_to_process.is_displayed():
                                try:
                                    key_child_xpath = ".//div[@data-testonly-column='Main Task ID']//span[@data-testid='text-type-display-span']"
                                    key_child = WebDriverWait(row_element_to_process, 1).until(
                                        EC.visibility_of_element_located((By.XPATH, key_child_xpath))
                                    )
                                    if key_child.is_displayed():
                                        is_row_visible_and_interactable = True
                                        add_log(f"Claimer DEBUG: Row Element ID {row_element_to_process.id} and key child are displayed.", "debug")
                                        break
                                except TimeoutException:
                                    add_log(f"Claimer DEBUG: Row Element ID {row_element_to_process.id} - key child NOT found/visible. Main row .is_displayed() was {row_element_to_process.is_displayed()}", "debug")
                                    if row_element_to_process.is_displayed():
                                        is_row_visible_and_interactable = True
                                        break
                            else:
                                add_log(f"Claimer DEBUG: Row Element ID {row_element_to_process.id} .is_displayed() is False on attempt {attempt+1}.", "debug")
                        except StaleElementReferenceException:
                            add_log(f"Claimer WARNING: Row Element ID {row_element_to_process.id if row_element_to_process else 'Unknown'} became stale during scroll/visibility check. Re-fetching for next attempt or skipping.", "warning")
                            if attempt < 1:
                                row_element_to_process = WebDriverWait(driver, 5).until(EC.presence_of_element_located((By.XPATH, current_row_xpath)))
                                continue
                            else: break
                        except Exception as e_scroll_vis:
                            add_log(f"Claimer DEBUG: Error during scroll/visibility check for Row Element ID {row_element_to_process.id if row_element_to_process else 'Unknown'} (attempt {attempt+1}): {e_scroll_vis}", "debug")
                            if attempt == 1: break

                    if not is_row_visible_and_interactable:
                        add_log(f"Claimer DEBUG: Row ID '{display_id_for_log_temp}' (Element ID: {row_element_to_process.id if row_element_to_process else 'N/A'}) ultimately considered NOT VISIBLE or interactable, skipping.", "debug")
                        continue

                    main_task_id_val = extract_field_data(row_element_to_process, "Main Task ID", default_value="")
                    row_id_attr_val = row_element_to_process.get_attribute("id")
                    display_id = main_task_id_val if main_task_id_val else (row_id_attr_val if row_id_attr_val else f"Row_Index_{i+1}_NoID")
                    display_id_for_log_temp = display_id

                    status = extract_field_data(row_element_to_process, "Status", default_value="Status Not Specified")
                    country_from_row = extract_field_data(row_element_to_process, "Country", default_value="Country Not Specified")
                    user_email_on_row = extract_field_data(row_element_to_process, "Useremail", span_sub_xpath="//span[@data-testid='email-type-display-span']", default_value="N/A")

                    add_log(f"Claimer Row Scan: Index {i+1}, ID='{display_id}', Country='{country_from_row}', Status='{status}', User='{user_email_on_row}' (Row Element ID: {row_element_to_process.id})", "info")

                    claim_this_case_for_country_slot = None
                    if country_from_row == "Portugal" and status == "Not Started" and not active_pt_case_exists:
                        claim_this_case_for_country_slot = "Portugal"
                    elif country_from_row == "Ghana" and status == "Not Started" and not active_gh_case_exists:
                        claim_this_case_for_country_slot = "Ghana"

                    if claim_this_case_for_country_slot:
                        add_log(f"Claimer: Potential claim for {claim_this_case_for_country_slot}: ID '{display_id}'. Attempting...", "info")

                        account_name = extract_field_data(row_element_to_process, "Account Name", default_value="N/A")
                        case_title = extract_field_data(row_element_to_process, "Case Title", default_value="N/A")
                        menu_link = extract_field_data(row_element_to_process, "Menu link", span_sub_xpath="//span[contains(@class, 'UrlTypeDisplay__text')]", default_value="N/A")
                        dish_photos_link = extract_field_data(row_element_to_process, "Dish Photos Link", span_sub_xpath="//span[contains(@class, 'UrlTypeDisplay__text')]", default_value="N/A")
                        menu_instructions = extract_field_data(row_element_to_process, "Menu instructions", default_value="N/A")
                        request_sent_date = extract_field_data(row_element_to_process, "Menu Request Sent Date", span_sub_xpath="//span[@data-testid='date-time-type-display-span']", default_value="N/A")
                        created_by = extract_field_data(row_element_to_process, "Created By", default_value="N/A")

                        try:
                            clickable_target = WebDriverWait(row_element_to_process, 10).until(
                                EC.element_to_be_clickable(row_element_to_process)
                            )
                            try:
                                clickable_target.click()
                            except ElementClickInterceptedException:
                                add_log(f"Claimer DEBUG: Direct click intercepted for {display_id}. Trying JS click.", "debug")
                                driver.execute_script("arguments[0].click();", clickable_target)

                            time.sleep(5)

                            sidebar_action_bar_xpath = "//div[contains(@class, 'SlideshowPage__action-bar')]"
                            detail_page_wait.until(EC.visibility_of_element_located((By.XPATH, sidebar_action_bar_xpath)))
                            start_task_button_xpath = "//span[@data-testonly-action='Start Task' and @data-testid='Start Task' and contains(@class, 'GenericActionButton')]"
                            start_task_button = detail_page_wait.until(EC.element_to_be_clickable((By.XPATH, start_task_button_xpath)))

                            ActionChains(driver).move_to_element(start_task_button).click().perform()
                            time.sleep(7)

                            claimed_case_details_to_return = {
                                "display_id": display_id, "row_id_attr": row_id_attr_val, "user_email": user_email_on_row,
                                "account_name": account_name, "case_title": case_title, "main_task_id": main_task_id_val,
                                "menu_link": menu_link, "dish_photos_link": dish_photos_link,
                                "country": claim_this_case_for_country_slot,
                                "status": f"In Progress (Claimed by Bot for {claim_this_case_for_country_slot})",
                                "menu_instructions": menu_instructions, "request_sent_date": request_sent_date,
                                "created_by": created_by, "claimed_time": time.strftime("%Y-%m-%d %H:%M:%S"),
                                "scraped_files_data": None
                            }
                            add_log(f"Claimer SUCCESS: Case '{display_id}' for {claim_this_case_for_country_slot} presumed claimed.", "success")
                            current_pass_status = f"CLAIM_SUCCESS_{claim_this_case_for_country_slot.upper()}"

                            url_to_scrape_for_case = None
                            compatible_domains = ["glovoapp.com", "ubereats.com", "wolt.com", "foodora.cz"]
                            if menu_link and menu_link != "N/A" and any(kw in menu_link.lower() for kw in compatible_domains):
                                url_to_scrape_for_case = menu_link
                            elif dish_photos_link and dish_photos_link != "N/A" and any(kw in dish_photos_link.lower() for kw in compatible_domains):
                                url_to_scrape_for_case = dish_photos_link

                            if url_to_scrape_for_case:
                                add_log(f"Auto-Scrape: Identified compatible link for case {display_id}: {url_to_scrape_for_case}", "info")
                                scraped_data = scrape_and_prepare_case_files(url_to_scrape_for_case, claim_this_case_for_country_slot, display_id)
                                if scraped_data:
                                    claimed_case_details_to_return["scraped_files_data"] = scraped_data
                                    add_log(f"Auto-Scrape: Successfully prepared files for case {display_id}.", "success")
                                else:
                                    add_log(f"Auto-Scrape: Failed to prepare files for case {display_id}.", "warning")
                            else:
                                add_log(f"Auto-Scrape: No compatible (Glovo/Uber/Wolt/Foodora) menu/photo link found for case {display_id}.", "info")

                            add_log(f"Claimer: Navigating back to AppSheet URL: {APPSHEET_URL} after claim.", "info")
                            driver.get(APPSHEET_URL)
                            time.sleep(5)
                            break # Exit row loop after successful claim

                        except WebDriverException as e_wd_claim:
                            add_log(f"Claimer CRITICAL: WebDriverException during claim process for '{display_id}' ({claim_this_case_for_country_slot}): {e_wd_claim}", "error")
                            traceback.print_exc()
                            current_pass_status = "DRIVER_DEAD_CLAIM_PROC"
                            try: driver.get(APPSHEET_URL); time.sleep(3)
                            except: add_log("Claimer: Also failed to navigate back after WebDriverException during claim.", "error")
                            break
                        except Exception as claim_err:
                            add_log(f"Claimer ERROR: Unexpected error during claim attempt for '{display_id}' ({claim_this_case_for_country_slot}): {claim_err}", "error")
                            traceback.print_exc()
                            try:
                                add_log("Claimer: Attempting to navigate back to AppSheet URL after claim error.", "info")
                                driver.get(APPSHEET_URL); time.sleep(3)
                            except WebDriverException as e_wd_nav_back:
                                add_log(f"Claimer CRITICAL: WebDriver error navigating back after failed claim: {e_wd_nav_back}", "error")
                                current_pass_status = "DRIVER_DEAD_NAV_BACK_FAIL" ; break
                            except Exception as e_nav_other:
                                add_log(f"Claimer ERROR navigating back (other): {e_nav_other}", "error")

                    # Logging colleague activity
                    bot_email_identifier = "BOT_CLAIMED"
                    # Ensure status variable is lowercased for comparison if AppSheet status can vary in case
                    current_row_status_lower = status.lower() if isinstance(status, str) else ""
                    if user_email_on_row and user_email_on_row != "N/A" and not (bot_email_identifier.lower() in user_email_on_row.lower()):
                        if current_row_status_lower in ["inprogress", "escalated", "completed"]:
                            # Corrected colleague_log_entry dictionary
                            colleague_log_entry = {
                                'Date': datetime.now().strftime('%Y-%m-%d'),
                                'Observed Timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                                'Claimed Timestamp': pd.NA,
                                'Finished Timestamp': pd.NA,
                                'Duration (seconds)': pd.NA,
                                'Duration (HH:MM:SS)': pd.NA,
                                'Case Display ID': display_id, # Use already extracted display_id
                                'Country': country_from_row, # Use already extracted country_from_row
                                'Assigned User': user_email_on_row, # Use already extracted user_email_on_row
                                'Status (Observed)': status, # Use already extracted status
                                # Re-extract or use previously stored if concerned about staleness for these specific fields
                                'Account Name': extract_field_data(row_element_to_process, "Account Name", default_value="N/A"),
                                'Case Title': extract_field_data(row_element_to_process, "Case Title", default_value="N/A"),
                                'Menu Link': extract_field_data(row_element_to_process, "Menu link", span_sub_xpath="//span[contains(@class, 'UrlTypeDisplay__text')]", default_value="N/A")
                            }
                            append_to_case_log(colleague_log_entry)

                except StaleElementReferenceException:
                    add_log(f"Claimer WARNING: Row at index {i+1} (last known ID: {display_id_for_log_temp}) became STALE before/during detail extraction. Skipping.", "warning"); continue
                except TimeoutException:
                    add_log(f"Claimer WARNING: Timeout locating/interacting with row at index {i+1} (last known ID: {display_id_for_log_temp}) before/during detail extraction. DOM might have changed. Skipping.", "warning"); continue
                except WebDriverException as e_wd_row_proc:
                    add_log(f"Claimer CRITICAL: WebDriverException processing row at index {i+1} (ID: {display_id_for_log_temp}): {e_wd_row_proc}", "error")
                    traceback.print_exc()
                    current_pass_status = "DRIVER_DEAD_ROW_PROC"; break
                except Exception as e_row_generic:
                    add_log(f"Claimer ERROR: Unexpected error processing row at index {i+1} (ID: {display_id_for_log_temp}): {e_row_generic}", "error")
                    traceback.print_exc()
                    continue

                if current_pass_status in ["DRIVER_DEAD_CLAIM_PROC", "DRIVER_DEAD_NAV_BACK_FAIL", "DRIVER_DEAD_ROW_PROC"]: break

    except WebDriverException as e_wd_outer_scope:
        add_log(f"Claimer CRITICAL: WebDriverException in outer scope of find_and_claim: {e_wd_outer_scope}", "error")
        traceback.print_exc()
        current_pass_status = "DRIVER_DEAD_OUTER_FCC"
    except Exception as e_outer_find_claim:
        add_log(f"Claimer MAJOR UNEXPECTED ERROR in find_and_claim_cases (outer try): {e_outer_find_claim}", "error")
        traceback.print_exc()
        current_pass_status = "ERROR_UNKNOWN_FCC_OUTER"

    message_to_queue = {
        "status": current_pass_status,
        "claimed_case_data": claimed_case_details_to_return
    }
    try:
        data_q.put_nowait(message_to_queue)
    except queue.Full:
        add_log("Claimer WARNING: Data queue is full when trying to send find_and_claim_cases result.", "warning")

    return current_pass_status

# --- Case Claimer: Main Loop for the Background Thread (Dash Context) ---
def run_claimer_loop(stop_event_ref: threading.Event):
    global monitoring_active_flag, claimer_status_message, active_portugal_case_store, active_ghana_case_store, data_queue_claimer

    driver = None
    thread_name = threading.current_thread().name
    add_log(f"Claimer THREAD ({thread_name}): Starting execution.", "info")

    try:
        claimer_status_message = "Claimer: Initializing WebDriver..."
        driver = initialize_claimer_driver()

        if driver is None:
            add_log(f"Claimer THREAD ({thread_name}): WebDriver initialization failed (driver is None). Thread stopping.", "error")
            data_queue_claimer.put_nowait({"status": "DRIVER_INIT_FAIL", "claimed_case_data": None})
            monitoring_active_flag = False
            return

        login_successful = check_claimer_login_status(driver)
        if not login_successful:
            add_log(f"Claimer THREAD ({thread_name}): Login check failed. Thread stopping.", "error")
            data_queue_claimer.put_nowait({"status": "LOGIN_FAIL", "claimed_case_data": None})
            monitoring_active_flag = False
            return

        claimer_status_message = "Claimer: Monitoring Active..."
        add_log(f"Claimer THREAD ({thread_name}): Monitoring started successfully (PT & GH).", "success")

        while not stop_event_ref.is_set():
            loop_start_time = time.time()

            pt_slot_free_at_loop_start = not bool(active_portugal_case_store)
            gh_slot_free_at_loop_start = not bool(active_ghana_case_store)
            find_status_result = "INIT_LOOP_PASS"

            if pt_slot_free_at_loop_start or gh_slot_free_at_loop_start:
                current_timestamp_hm = time.strftime('%H:%M:%S')
                if not any(err_kw in claimer_status_message.upper() for err_kw in ["ERROR", "FAILED", "CRITICAL", "STOP", "DEAD"]):
                    claimer_status_message = f"Claimer: Checking for cases (PT free: {pt_slot_free_at_loop_start}, GH free: {gh_slot_free_at_loop_start})... ({current_timestamp_hm})"

                add_log(f"Claimer THREAD ({thread_name}): Calling find_and_claim_cases. PT_free={pt_slot_free_at_loop_start}, GH_free={gh_slot_free_at_loop_start}", "debug")
                try:
                    find_status_result = find_and_claim_cases(driver, data_queue_claimer, stop_event_ref)
                    add_log(f"Claimer THREAD ({thread_name}): find_and_claim_cases returned status: {find_status_result}", "debug")
                except Exception as e_fcc_call:
                    add_log(f"Claimer THREAD ({thread_name}): UNCAUGHT EXCEPTION from find_and_claim_cases call: {e_fcc_call}", "error")
                    traceback.print_exc()
                    find_status_result = "EXCEPTION_CALLING_FCC"
                    claimer_status_message = "Claimer Error: Uncaught exception from find_and_claim_cases. Check logs."

                critical_statuses = [
                    "DRIVER_DEAD_PRE_CHECK", "DRIVER_DEAD_RESP_CHECK", "DRIVER_DEAD_ROW_FIND",
                    "DRIVER_DEAD_ROW_PROC", "DRIVER_DEAD_CLAIM_PROC", "DRIVER_DEAD_NAV_BACK_FAIL",
                    "DRIVER_DEAD_OUTER_FCC", "EXCEPTION_CALLING_FCC", "ERROR_UNEXPECTED_FINDING_ROWS",
                    "ERROR_UNKNOWN_FCC_OUTER" # Removed THREAD_OUTER_EXCEPTION as it's from this loop's handler
                ]

                if find_status_result in critical_statuses:
                    claimer_status_message = f"Claimer CRITICAL: Fatal issue detected ({find_status_result}). Forcing stop."
                    add_log(f"Claimer THREAD ({thread_name}): {claimer_status_message}", "error")
                    stop_event_ref.set()
                elif find_status_result == "STOPPED":
                    add_log(f"Claimer THREAD ({thread_name}): find_and_claim_cases or internal check reported stop. Loop will exit.", "info")
                elif "CLAIM_SUCCESS" in find_status_result:
                    claimed_country_from_status = find_status_result.split('_')[-1]
                    claimer_status_message = f"Claimer: Successfully processed claim for {claimed_country_from_status}."
                    add_log(f"Claimer THREAD ({thread_name}): {claimer_status_message}", "info")
                    add_log(f"Claimer THREAD ({thread_name}): Pausing for 3s after successful claim of {claimed_country_from_status} case.", "debug")
                    time.sleep(3)
                elif find_status_result == "OK_BOTH_SLOTS_FULL":
                     if not any(err_kw in claimer_status_message.upper() for err_kw in ["ERROR", "FAILED", "CRITICAL", "STOP", "DEAD"]):
                        claimer_status_message = f"Claimer: Both PT & GH slots full. Waiting... ({current_timestamp_hm})"
                else: # Handles OK_NO_ROWS_VISIBLE, OK_TIMEOUT_NO_ROWS, OK_NO_NEW_CLAIMABLE_SLOT_OR_CASE etc.
                    if not any(err_kw in claimer_status_message.upper() for err_kw in ["ERROR", "FAILED", "CRITICAL", "STOP", "DEAD"]):
                        claimer_status_message = f"Claimer: No new suitable case or slot. Status: {find_status_result}. ({current_timestamp_hm})"
            else:
                if not any(err_kw in claimer_status_message.upper() for err_kw in ["ERROR", "FAILED", "CRITICAL", "STOP", "DEAD"]):
                    claimer_status_message = f"Claimer: Both PT & GH slots full. Waiting... ({time.strftime('%H:%M:%S')})"

            if stop_event_ref.is_set():
                add_log(f"Claimer THREAD ({thread_name}): Stop event detected before/during main loop wait. Breaking from while loop.", "debug"); break

            loop_duration = time.time() - loop_start_time
            wait_time_seconds = max(0.1, 7.0 - loop_duration)

            for _ in range(int(wait_time_seconds * 20)):
                if stop_event_ref.is_set(): break
                time.sleep(0.05)

            if stop_event_ref.is_set():
                add_log(f"Claimer THREAD ({thread_name}): Stop event detected after inner wait. Breaking from while loop.", "debug"); break

        add_log(f"Claimer THREAD ({thread_name}): Exited main while loop. stop_event.is_set() = {stop_event_ref.is_set()}", "info")
        if stop_event_ref.is_set() and not any(err_kw in claimer_status_message.upper() for err_kw in ["CRITICAL", "FAIL", "ERROR", "DEAD"]):
            claimer_status_message = "Claimer: Monitoring stopped by user."

    except Exception as thread_err:
        claimer_status_message = f"Claimer THREAD ({thread_name}): Outer Critical Thread Error during execution. Check logs."
        add_log(f"Claimer THREAD ({thread_name}): {claimer_status_message} Details: {thread_err}", "error")
        traceback.print_exc()
        if stop_event_ref and not stop_event_ref.is_set():
            stop_event_ref.set()
        try: data_queue_claimer.put_nowait({"status": "THREAD_OUTER_EXCEPTION", "claimed_case_data": None})
        except queue.Full: add_log(f"Claimer THREAD ({thread_name}): Data queue full on THREAD_OUTER_EXCEPTION.", "warning")

    finally:
        add_log(f"Claimer THREAD ({thread_name}): Starting cleanup (finally block).", "info")
        if driver:
            add_log(f"Claimer THREAD ({thread_name}): Attempting to quit WebDriver.", "info")
            try: driver.quit()
            except Exception as qe: add_log(f"Claimer THREAD ({thread_name}): Error quitting WebDriver in finally: {qe}", "warning")

        monitoring_active_flag = False

        final_status_suffix = " Claimer shut down."
        if stop_event_ref and stop_event_ref.is_set():
            if any(err_kw in claimer_status_message.upper() for err_kw in ["CRITICAL", "FAIL", "ERROR", "DEAD", "EXCEPTION"]):
                if "shut down" not in claimer_status_message.lower():
                    claimer_status_message += final_status_suffix
            elif "stopped by user" not in claimer_status_message.lower() and "shut down" not in claimer_status_message.lower():
                claimer_status_message = "Claimer: Monitoring stopped by user." + final_status_suffix
            elif "shut down" not in claimer_status_message.lower():
                claimer_status_message += final_status_suffix
        elif "shut down" not in claimer_status_message.lower():
             claimer_status_message += final_status_suffix

        if stop_event_ref and not stop_event_ref.is_set():
            stop_event_ref.set()
            add_log(f"Claimer THREAD ({thread_name}): stop_event was NOT set in finally, setting it now (e.g. normal loop completion or unhandled exit).", "warning")

        add_log(f"Claimer THREAD ({thread_name}): Final status message for UI: '{claimer_status_message}'", "info")
        add_log(f"Claimer THREAD ({thread_name}): Background thread finished execution.", "info")

# --- Case Claimer: Main Loop for the Background Thread (Dash Context) ---


# (This code starts with the Dash app layout and callbacks, and includes the main app execution)
# (It assumes Part 1, Part 2 (scraper, PDF logic), and Part 3 (claimer logic) 
#  are already in place above this block.)

# --- Dash App Initialization ---
app = dash.Dash(__name__, suppress_callback_exceptions=True, prevent_initial_callbacks='initial_duplicate')
app.title = "Universal Operations Hub"

# --- Dash App Layout ---
# (Your existing style definitions: dark_theme_styles, input_style, button_style, etc. remain here)
dark_theme_styles = {
    'backgroundColor': '#1E1E1E',
    'color': '#E0E0E0',
    'fontFamily': 'Arial, sans-serif',
    'margin': '0',
    'padding': '0',
    'height': '100vh',
    'overflow': 'hidden'
}
input_style = {
    'backgroundColor': '#252526', 'color': '#E0E0E0',
    'border': '1px solid #3E3E3E', 'borderRadius': '5px',
    'padding': '8px', 'width': '95%', 'marginBottom': '10px', 'marginTop': '5px'
}
button_style = {
    'backgroundColor': '#4CAF50', 'color': 'white', 'border': 'none',
    'padding': '10px 15px', 'textAlign': 'center', 'textDecoration': 'none',
    'display': 'inline-block', 'fontSize': '14px', 'margin': '4px 2px',
    'cursor': 'pointer', 'borderRadius': '5px'
}
disabled_button_style = {**button_style, 'backgroundColor': '#555', 'cursor': 'not-allowed'}
textarea_style = {
    'width': '100%',
    'backgroundColor': '#252526', 'color': '#E0E0E0',
    'border': '1px solid #3E3E3E', 'borderRadius': '5px', 'padding': '5px'
}
card_style = {
    'backgroundColor': '#2a2a2e', 'border': '1px solid #4CAF50',
    'borderRadius': '8px', 'padding': '15px', 'marginBottom': '15px'
}
section_style = {
    'padding': '15px', 'border': '1px solid #333',
    'borderRadius': '5px', 'margin':'10px', 'flex': '1'
}

SIDEBAR_STYLE_VISIBLE = {
    'padding': '15px', 'borderRight': '1px solid #444',
    'minWidth': '350px', 'maxWidth': '30%',
    'height':'calc(100vh - 80px)',
    'overflowY': 'auto',
    'backgroundColor': '#252526',
    'display': 'block',
    'transition': 'all 0.3s ease-in-out'
}
SIDEBAR_STYLE_HIDDEN = {
    **SIDEBAR_STYLE_VISIBLE,
    'minWidth': '0px', 'maxWidth': '0px', 'width': '0px',
    'padding': '0px', 'overflow': 'hidden',
    'borderRight': 'none'
}
MAIN_CONTENT_STYLE_FULL = {
    'padding': '15px', 'flex': '1',
    'height':'calc(100vh - 80px)',
    'overflowY': 'auto',
    'marginLeft': '0px',
    'transition': 'all 0.3s ease-in-out',
    'width': '100%'
}
MAIN_CONTENT_STYLE_WITH_SIDEBAR = {
    'padding': '15px', 'flex': '1',
    'height':'calc(100vh - 80px)',
    'overflowY': 'auto',
    'transition': 'all 0.3s ease-in-out'
}


app.layout = html.Div(style=dark_theme_styles, children=[
    dcc.Location(id='url', refresh=False),
    html.Div(style={'display': 'flex', 'justifyContent':'space-between', 'alignItems':'center', 'paddingRight':'20px'}, children=[
        html.H1("⚙️ Universal Operations Hub - Dash Version", style={'textAlign': 'center', 'color': '#4CAF50', 'marginBottom': '0px', 'padding':'10px 0', 'flexGrow':'1'}),
        html.Button("Toggle Sidebar", id="sidebar-toggle-button", style={**button_style, 'backgroundColor':'#007BFF', 'height':'fit-content'})
    ]),
    html.Hr(style={'borderColor':'#444', 'marginTop':'0px'}),

    dcc.Store(id='claimer-thread-status-store'),
    dcc.Store(id='active-pt-case-data-store', data={}),
    dcc.Store(id='active-gh-case-data-store', data={}),
    dcc.Store(id='web-scraper-output-store', data={'timestamp': None, 'excel_bytes': None, 'excel_name': None, 'zip_bytes': None, 'zip_name': None}),
    dcc.Store(id='local-image-output-store', data={'timestamp': None, 'zip_bytes': None, 'zip_name': None}),
    dcc.Store(id='pdf-output-store', data={'timestamp': None, 'excel_bytes': None, 'excel_name': None, 'zip_bytes': None, 'zip_name': None}),
    dcc.Store(id='auto-scrape-pt-store', data={'timestamp': None}),
    dcc.Store(id='auto-scrape-gh-store', data={'timestamp': None}),
    dcc.Store(id='sidebar-data-store', data={'timestamp': None, 'bot_log_data': None, 'leaderboard_data': None, 'monthly_leaderboard_data': None, 'daily_leaderboard_case_details_log': None}),
    dcc.Store(id='processing-flags-store', data={'scraping': False, 'local_processing': False, 'pdf_processing': False, 'claiming': False}),
    dcc.Store(id='uploaded-local-images-store', data=[]),
    dcc.Store(id='uploaded-pdf-files-store', data=[]),
    dcc.Store(id='sidebar-state-store', data={'is_collapsed': False}),

    html.Div(id='hidden-trigger-div', style={'display': 'none'}),

    dcc.Interval(id='interval-log-update', interval=2*1000, n_intervals=0),
    dcc.Interval(id='interval-status-update', interval=1*1000, n_intervals=0),
    dcc.Interval(id='interval-active-cases-refresh', interval=3*1000, n_intervals=0),

    dcc.Download(id="download-excel-web"), dcc.Download(id="download-zip-web"),
    dcc.Download(id="download-zip-local"),
    dcc.Download(id="download-excel-pdf"), dcc.Download(id="download-zip-pdf"),
    dcc.Download(id="download-auto-excel-pt"), dcc.Download(id="download-auto-zip-pt"),
    dcc.Download(id="download-auto-excel-gh"), dcc.Download(id="download-auto-zip-gh"),

    html.Div(id="app-container", className="row", style={'display': 'flex', 'flexDirection': 'row', 'height': 'calc(100vh - 80px)'}, children=[
        html.Div(id='sidebar', style=SIDEBAR_STYLE_VISIBLE, children=[
            html.H3("📋 Case Activity Log", style={'color': '#4CAF50'}),
            dcc.DatePickerSingle(
                id='log-date-picker',
                min_date_allowed=datetime(2020, 1, 1),
                max_date_allowed=datetime.now().date() + timedelta(days=1),
                initial_visible_month=datetime.now().date(),
                date=datetime.now().date(),
                display_format='YYYY-MM-DD',
                style={'marginBottom': '10px', 'width':'100%'}
            ),
            html.Button("Load Daily Activity", id="load-log-button", style=button_style),
            html.Hr(style={'borderColor':'#444'}),
            html.H4("Bot's Activity (Selected Day)", style={'color': '#66BB6A'}),
            html.Div(id='bot-activity-table-div'),
            html.Hr(style={'borderColor':'#444'}),
            html.H4("Daily Team Leaderboard", style={'color': '#66BB6A'}),
            html.Div(id='leaderboard-table-div', children=[ # Outer container for table + message
                dash_table.DataTable(
                    id='daily-leaderboard-table', 
                    columns=[], 
                    data=[],    
                    style_cell={'textAlign': 'left', 'backgroundColor': '#252526', 'color': '#E0E0E0', 'border': '1px solid #3E3E3E', 'fontSize': '12px'},
                    style_header={'backgroundColor': '#007BFF', 'fontWeight': 'bold', 'color': 'white'},
                    sort_action="native",
                    active_cell=None 
                ),
                html.Div(id='daily-leaderboard-status-message', style={'marginTop':'5px'}) 
            ]),
            html.Div(id='daily-leaderboard-case-details-div', style={'marginTop':'10px'}),
            
            html.Hr(style={'borderColor':'#444'}),
            html.H4("Monthly Team Leaderboard", style={'color': '#66BB6A'}),
            dcc.Dropdown(
                id='month-picker',
                options=[{'label': datetime(2000, i, 1).strftime('%B'), 'value': i} for i in range(1, 13)],
                placeholder="Select Month",
                style={'marginBottom': '10px', 'color':'#333'}
            ),
            dcc.Input(
                id='year-picker',
                type='number',
                placeholder="Enter Year (e.g., 2024)",
                value=datetime.now().year,
                style=input_style
            ),
            html.Button("Load Monthly Leaderboard", id="load-monthly-leaderboard-button", style=button_style),
            html.Div(id='monthly-leaderboard-table-div', style={'marginTop':'10px'})
        ]),

        html.Div(id="main-content", className="nine columns", style=MAIN_CONTENT_STYLE_WITH_SIDEBAR, children=[
            html.Div(className="row", style={'display': 'flex', 'flexDirection': 'row', 'marginBottom':'20px'}, children=[
                html.Div(className="six columns", style=section_style, children=[
                    html.H4("Auto Case Operator"),
                    html.Div(id='claimer-controls-div', children=[
                        html.Button("▶️ Start Monitoring", id="claimer-start-stop-button", style=button_style)
                    ]),
                    html.Div(id="claimer-monitoring-caption", children=[
                        html.P("⚠️ Click 'Stop Monitoring' firmly.", style={'fontSize': 'small', 'color': '#aaa'})
                    ], style={'display': 'none', 'marginTop':'5px'}),
                    dcc.Textarea(id='claimer-status-display', value=claimer_status_message, style={**textarea_style, 'height': '80px', 'marginTop':'10px'}, readOnly=True),
                ]),
                html.Div(className="six columns", style=section_style, children=[
                    html.H4("⚡ Active Cases"),
                    html.Div(id='active-cases-display', children="No active cases."),
                    html.P(id='active-cases-refresh-timestamp', style={'fontSize': 'small', 'color': '#aaa', 'marginTop':'5px'})
                ]),
            ]),
            html.Hr(style={'borderColor':'#444'}),

            html.Div(className="row", style={'display': 'flex', 'flexDirection': 'row', 'flexWrap':'wrap'}, children=[
                html.Div(style=section_style, children=[
                    html.H4("1. Scrape Menu from Web 🌐"),
                    dcc.Dropdown(id='scraper-country-dropdown', options=[{'label': c, 'value': c} for c in ["Portugal", "Ghana", "Czechia"]], value='Portugal', style={'marginBottom': '10px', 'color': '#333'}),
                    dcc.Input(id='scraper-url-input', type='text', placeholder='Enter Menu URL...', style=input_style),
                    html.Button("🚀 Start Scraping", id='scraper-start-button', style=button_style),
                    html.Div(id='scraper-status-placeholder', style={'marginTop': '10px'}),
                    html.Div(id='scraper-download-area', children=[
                        html.Button("💾 Excel", id="scraper-download-excel-button", style={**button_style, 'display':'none', 'marginRight':'5px'}),
                        html.Button("🖼️ Images ZIP", id="scraper-download-zip-button", style={**button_style, 'display':'none'})
                    ], style={'marginTop':'10px'})
                ]),
                html.Div(style=section_style, children=[
                    html.H4("2. Process Local Images 🖼️"),
                    dcc.Upload(id='local-image-uploader', children=html.Div(['Drag/Drop or ', html.A('Select Images')]), style={'width': '95%', 'height': '60px', 'lineHeight': '60px', 'borderWidth': '1px', 'borderStyle': 'dashed', 'borderRadius': '5px', 'textAlign': 'center', 'margin': '10px auto', 'color': '#aaa'}, multiple=True),
                    html.Div(id='local-image-upload-status'),
                    html.Button("⚙️ Process Images", id='local-image-process-button', style=button_style),
                    html.Div(id='local-image-status-placeholder', style={'marginTop': '10px'}),
                    html.Div(id='local-image-download-area', children=[
                         html.Button("🖼️ Download ZIP", id="local-image-download-zip-button", style={**button_style, 'display':'none'})
                    ], style={'marginTop':'10px'})
                ]),
                html.Div(style=section_style, children=[
                    html.H4("3. Extract Data from PDF 📄"),
                    dcc.Dropdown(id='pdf-country-dropdown', options=[{'label': c, 'value': c} for c in ["Portugal", "Ghana", "Czechia"]], value='Portugal', style={'marginBottom': '10px', 'color': '#333'}),
                    dcc.Upload(id='pdf-file-uploader', children=html.Div(['Drag/Drop or ', html.A('Select PDFs')]), style={'width': '95%', 'height': '60px', 'lineHeight': '60px', 'borderWidth': '1px', 'borderStyle': 'dashed', 'borderRadius': '5px', 'textAlign': 'center', 'margin': '10px auto', 'color': '#aaa'}, multiple=True),
                    html.Div(id='pdf-upload-status'),
                    html.Button("📄 Process PDF(s)", id='pdf-process-button', style=button_style),
                    html.Div(id='pdf-status-placeholder', style={'marginTop': '10px'}),
                    html.Div(id='pdf-download-area', children=[
                        html.Button("💾 Excel", id="pdf-download-excel-button", style={**button_style, 'display':'none', 'marginRight':'5px'}),
                        html.Button("🖼️ Images ZIP", id="pdf-download-zip-button", style={**button_style, 'display':'none'})
                    ], style={'marginTop':'10px'})
                ]),
            ]),
            html.Hr(style={'borderColor':'#444', 'marginTop':'20px'}),
            html.Details([
                html.Summary('📜 Live Log', style={'cursor': 'pointer', 'color': '#4CAF50', 'fontSize': '1.2em', 'marginBottom':'10px'}),
                dcc.Textarea(id='live-log-display', value="Log initialized...\n", style={**textarea_style, 'height':'300px'}, readOnly=True)
            ], open=True, style={'marginTop': '20px'}),
        ]) 
    ]) 
])

# --- Dash Callbacks ---

@app.callback(
    [Output('sidebar', 'style'),
     Output('main-content', 'style'),
     Output('sidebar-state-store', 'data')],
    [Input('sidebar-toggle-button', 'n_clicks')],
    [State('sidebar-state-store', 'data')],
    prevent_initial_call=True
)
def toggle_sidebar(n_clicks_toggle, sidebar_state):
    if not n_clicks_toggle:
        return dash.no_update, dash.no_update, dash.no_update

    new_state_is_collapsed = not sidebar_state.get('is_collapsed', False)
    if new_state_is_collapsed:
        sidebar_style_to_set = SIDEBAR_STYLE_HIDDEN
        main_content_style_to_set = MAIN_CONTENT_STYLE_FULL
    else:
        sidebar_style_to_set = SIDEBAR_STYLE_VISIBLE
        main_content_style_to_set = MAIN_CONTENT_STYLE_WITH_SIDEBAR
    
    return sidebar_style_to_set, main_content_style_to_set, {'is_collapsed': new_state_is_collapsed}

@app.callback(Output('live-log-display', 'value'),
              Input('interval-log-update', 'n_intervals'))
def update_log_display_callback(n_intervals_log):
    global app_log_messages
    return "\n".join(app_log_messages)

@app.callback(
    [Output('claimer-status-display', 'value'),
     Output('claimer-controls-div', 'children'),
     Output('claimer-monitoring-caption', 'style')],
    [Input('interval-status-update', 'n_intervals'),
     Input('processing-flags-store', 'data')]
)
def update_claimer_ui(n_intervals_status, processing_flags):
    global claimer_status_message, monitoring_active_flag
    is_other_process_running = processing_flags.get('scraping', False) or \
                               processing_flags.get('local_processing', False) or \
                               processing_flags.get('pdf_processing', False) or \
                               processing_flags.get('claiming', False)
    
    claimer_btn_disabled_status = ("Starting..." in claimer_status_message) or \
                                  ("Stopping..." in claimer_status_message) or \
                                  ("Initializing..." in claimer_status_message)
    
    if monitoring_active_flag:
        controls_children = [
            html.Div(style={'display':'flex'}, children=[
                html.Button("🔄 Refresh UI", id="claimer-refresh-button", style={**button_style, 'backgroundColor': '#007BFF', 'marginRight':'10px'}, disabled=claimer_btn_disabled_status),
                html.Button("⏹️ Stop Monitoring", id="claimer-start-stop-button", style=button_style if not claimer_btn_disabled_status else disabled_button_style, disabled=claimer_btn_disabled_status)
            ])
        ]
        caption_style = {'display': 'block', 'fontSize': 'small', 'color': '#aaa', 'marginTop':'5px'}
    else:
        controls_children = [
            html.Button("▶️ Start Monitoring", id="claimer-start-stop-button", style=button_style if not claimer_btn_disabled_status else disabled_button_style, disabled=claimer_btn_disabled_status)
        ]
        caption_style = {'display': 'none'}
    return claimer_status_message, controls_children, caption_style

@app.callback(
    Output('claimer-thread-status-store', 'data', allow_duplicate=True),
    Input('claimer-start-stop-button', 'n_clicks'),
    State('processing-flags-store', 'data'),
    prevent_initial_call=True
)
def toggle_monitoring(n_clicks_toggle_claimer, current_processing_flags):
    global monitoring_active_flag, stop_event_claimer, claimer_thread_instance, claimer_status_message, data_queue_claimer
    global active_portugal_case_store, active_ghana_case_store

    if not n_clicks_toggle_claimer:
        return dash.no_update

    output_store_data = {'timestamp': time.time(), 'monitoring_active': monitoring_active_flag}

    if monitoring_active_flag:
        add_log("UI: 'Stop Monitoring' button clicked.", "info")
        if stop_event_claimer: stop_event_claimer.set()
        claimer_status_message = "Claimer: Stop requested... Awaiting thread termination."
        output_store_data['monitoring_active'] = False
    else:
        add_log("UI: 'Start Monitoring' button clicked.", "info")
        if not USER_DATA_DIR or not os.path.isdir(USER_DATA_DIR) or "2407850" not in USER_DATA_DIR: 
            claimer_status_message = f"CRITICAL: USER_DATA_DIR ('{USER_DATA_DIR}') incorrect or not found. Please update the script."
            add_log(claimer_status_message, "error")
            return {'timestamp': time.time(), 'status': 'user_data_dir_error', 'monitoring_active': False}

        active_portugal_case_store.clear()
        active_ghana_case_store.clear()
        while not data_queue_claimer.empty():
            try: data_queue_claimer.get_nowait()
            except queue.Empty: break
        
        monitoring_active_flag = True
        stop_event_claimer.clear()
        claimer_status_message = "Claimer: Starting..."
        if not isinstance(data_queue_claimer, queue.Queue): data_queue_claimer = queue.Queue()
        
        claimer_thread_instance = threading.Thread(target=run_claimer_loop, args=(stop_event_claimer,), daemon=True) 
        claimer_thread_instance.start()
        add_log("Claimer monitoring thread initiated.", "info")
        output_store_data['monitoring_active'] = True
    
    return output_store_data

@app.callback(
    Output('hidden-trigger-div', 'children', allow_duplicate=True),
    Input('claimer-refresh-button', 'n_clicks'),
    prevent_initial_call=True
)
def manual_refresh_ui(n_clicks_refresh):
    if n_clicks_refresh and n_clicks_refresh > 0:
        add_log("UI: Manual Refresh button clicked (claimer UI).", "info")
    return f"manual_claimer_refreshed_at_{time.time()}"

@app.callback(
    [Output('active-cases-display', 'children'),
     Output('active-cases-refresh-timestamp', 'children'),
     Output('active-pt-case-data-store', 'data', allow_duplicate=True),
     Output('active-gh-case-data-store', 'data', allow_duplicate=True)
    ],
    [Input('interval-active-cases-refresh', 'n_intervals'),
     Input('claimer-thread-status-store', 'data')],
    prevent_initial_call=True 
)
def update_active_cases_display(n_intervals_active_case, claimer_thread_trigger_data):
    global active_portugal_case_store, active_ghana_case_store, data_queue_claimer

    new_pt_case_data_for_store = dash.no_update
    new_gh_case_data_for_store = dash.no_update

    children = []
    try:
        while not data_queue_claimer.empty():
            queued_message = data_queue_claimer.get_nowait()
            q_status = queued_message.get("status")
            claimed_data_in_q = queued_message.get("claimed_case_data")
            add_log(f"Dash UI (Active Cases): Processing Q msg: Status '{q_status}'", "debug")

            if "CLAIM_SUCCESS" in q_status and claimed_data_in_q:
                country = claimed_data_in_q.get("country")
                if country == "Portugal": 
                    active_portugal_case_store = claimed_data_in_q
                    new_pt_case_data_for_store = claimed_data_in_q 
                elif country == "Ghana": 
                    active_ghana_case_store = claimed_data_in_q
                    new_gh_case_data_for_store = claimed_data_in_q
            elif q_status in ["DRIVER_INIT_FAIL", "LOGIN_FAIL", "THREAD_EXCEPTION", "DRIVER_DEAD_PRE_CHECK", "DRIVER_DEAD"]:
                active_portugal_case_store.clear()
                active_ghana_case_store.clear()
                new_pt_case_data_for_store = {} 
                new_gh_case_data_for_store = {} 
                add_log(f"Dash UI: Claimer thread issue '{q_status}', clearing active case stores and globals.", "warning")

    except queue.Empty: pass
    except Exception as e: add_log(f"Dash UI: Error processing claimer queue for active cases display: {e}", "error")

    if not active_portugal_case_store and not active_ghana_case_store:
        children.append(html.Div("No active cases being handled by the bot.", style=card_style))
    
    if active_portugal_case_store:
        case = active_portugal_case_store
        card_content = [
            html.H5(f"Portugal Case 🇵🇹 - Task ID: {case.get('display_id', 'N/A')}", style={'color':'#66BB6A'}),
            html.P(f"Account: {case.get('account_name', 'N/A')}"),
            html.P(f"Title: {case.get('case_title', 'N/A')}") 
        ] 
        scraped_files = case.get("scraped_files_data")
        if scraped_files:
            card_content.append(html.H6("Auto-Scraped Files:", style={'marginTop':'10px'}))
            if scraped_files.get("excel_bytes") and scraped_files.get("excel_name"):
                 card_content.append(html.Button(f"📄 Excel ({scraped_files.get('excel_name')})", id={'type':'auto-download-btn', 'index': 'pt-excel'}, style=button_style))
            if scraped_files.get("zip_bytes") and scraped_files.get("zip_name"):
                 card_content.append(html.Button(f"🖼️ Images ZIP ({scraped_files.get('zip_name')})", id={'type':'auto-download-btn', 'index': 'pt-zip'}, style={**button_style, 'marginLeft':'5px'}))
        card_content.append(html.Button("✅ Finish Portugal Case", id={'type': 'finish-case-button', 'index': 'pt'}, style={**button_style, 'marginTop':'10px', 'backgroundColor':'#d9534f'}))
        children.append(html.Div(card_content, style=card_style))

    if active_ghana_case_store:
        case = active_ghana_case_store
        card_content = [
            html.H5(f"Ghana Case 🇬🇭 - Task ID: {case.get('display_id', 'N/A')}", style={'color':'#66BB6A'}),
            html.P(f"Account: {case.get('account_name', 'N/A')}"),
            html.P(f"Title: {case.get('case_title', 'N/A')}") 
        ] 
        scraped_files = case.get("scraped_files_data")
        if scraped_files:
            card_content.append(html.H6("Auto-Scraped Files:", style={'marginTop':'10px'}))
            if scraped_files.get("excel_bytes") and scraped_files.get("excel_name"):
                card_content.append(html.Button(f"📄 Excel ({scraped_files.get('excel_name')})", id={'type':'auto-download-btn', 'index': 'gh-excel'}, style=button_style))
            if scraped_files.get("zip_bytes") and scraped_files.get("zip_name"):
                card_content.append(html.Button(f"🖼️ Images ZIP ({scraped_files.get('zip_name')})", id={'type':'auto-download-btn', 'index': 'gh-zip'}, style={**button_style, 'marginLeft':'5px'}))
        card_content.append(html.Button("✅ Finish Ghana Case", id={'type': 'finish-case-button', 'index': 'gh'}, style={**button_style, 'marginTop':'10px', 'backgroundColor':'#d9534f'}))
        children.append(html.Div(card_content, style=card_style))
        
    timestamp_text = f"Active cases view updated: {time.strftime('%H:%M:%S')}"
    return children, timestamp_text, new_pt_case_data_for_store, new_gh_case_data_for_store

@app.callback(
    [Output('active-pt-case-data-store', 'data', allow_duplicate=True),
     Output('active-gh-case-data-store', 'data', allow_duplicate=True)],
    [Input({'type': 'finish-case-button', 'index': dash.ALL}, 'n_clicks')],
    prevent_initial_call=True
)
def finish_case_callback(n_clicks_finish):
    ctx = dash.callback_context
    if not ctx.triggered or not any(n_clicks_finish):
        return dash.no_update, dash.no_update

    triggered_button_id_dict = json.loads(ctx.triggered[0]['prop_id'].split('.')[0])
    country_index = triggered_button_id_dict.get('index')

    updated_pt_store = dash.no_update
    updated_gh_store = dash.no_update

    case_to_finish_details = None
    if country_index == 'pt' and active_portugal_case_store:
        case_to_finish_details = active_portugal_case_store.copy()
        active_portugal_case_store.clear()
        updated_pt_store = {}
        add_log(f"UI: 'Finish Portugal Case' processing for Task ID: {case_to_finish_details.get('display_id', 'N/A')}", "info")
    elif country_index == 'gh' and active_ghana_case_store:
        case_to_finish_details = active_ghana_case_store.copy()
        active_ghana_case_store.clear()
        updated_gh_store = {}
        add_log(f"UI: 'Finish Ghana Case' processing for Task ID: {case_to_finish_details.get('display_id', 'N/A')}", "info")
    else:
        add_log(f"UI: Finish button for '{country_index}' clicked, but no active case in global store.", "warning")
        return dash.no_update, dash.no_update

    if case_to_finish_details:
        finish_time_obj = datetime.now()
        calculated_duration_seconds = None
        if case_to_finish_details.get("claimed_time"):
            try:
                claimed_datetime_obj = datetime.strptime(case_to_finish_details["claimed_time"], "%Y-%m-%d %H:%M:%S")
                calculated_duration_seconds = (finish_time_obj - claimed_datetime_obj).total_seconds()
            except ValueError:
                add_log(f"Warning: Could not parse claimed_time '{case_to_finish_details.get('claimed_time')}' for duration.", "warning")

        log_entry_to_append = {
            'Date': finish_time_obj.strftime('%Y-%m-%d'),
            'Observed Timestamp': finish_time_obj.strftime('%Y-%m-%d %H:%M:%S'),
            'Claimed Timestamp': case_to_finish_details.get("claimed_time", pd.NA),
            'Finished Timestamp': finish_time_obj.strftime('%Y-%m-%d %H:%M:%S'),
            'Duration (seconds)': calculated_duration_seconds if calculated_duration_seconds is not None else pd.NA,
            'Duration (HH:MM:SS)': format_duration(calculated_duration_seconds) if calculated_duration_seconds is not None else pd.NA, 
            'Case Display ID': case_to_finish_details.get('display_id', 'N/A'),
            'Country': case_to_finish_details.get('country', 'N/A'),
            'Assigned User': "BOT_CLAIMED", 
            'Status (Observed)': "Completed", 
            'Account Name': case_to_finish_details.get('account_name', 'N/A'),
            'Case Title': case_to_finish_details.get('case_title', 'N/A'),
            'Menu Link': case_to_finish_details.get('menu_link', 'N/A')
        }
        append_to_case_log(log_entry_to_append) 
        add_log(f"Case '{case_to_finish_details.get('display_id')}' for {case_to_finish_details.get('country')} marked finished and logged.", "success")
        
    return updated_pt_store, updated_gh_store

@app.callback(
    Output("download-auto-excel-pt", "data"),
    Input({'type': 'auto-download-btn', 'index': 'pt-excel'}, 'n_clicks'),
    State('active-pt-case-data-store', 'data'),
    prevent_initial_call=True
)
def download_auto_pt_excel(n_clicks_dl, pt_case_data_from_store):
    if not n_clicks_dl or not pt_case_data_from_store: raise dash.exceptions.PreventUpdate
    scraped_data_nested = pt_case_data_from_store.get("scraped_files_data", {})
    if not scraped_data_nested.get('excel_bytes'): raise dash.exceptions.PreventUpdate
    return dict(content=scraped_data_nested['excel_bytes'], filename=scraped_data_nested.get('excel_name', 'auto_scraped_pt.xlsx'), base64=True)

@app.callback(
    Output("download-auto-zip-pt", "data"),
    Input({'type': 'auto-download-btn', 'index': 'pt-zip'}, 'n_clicks'),
    State('active-pt-case-data-store', 'data'), 
    prevent_initial_call=True
)
def download_auto_pt_zip(n_clicks_dl, pt_case_data_from_store):
    if not n_clicks_dl or not pt_case_data_from_store: raise dash.exceptions.PreventUpdate
    scraped_data_nested = pt_case_data_from_store.get("scraped_files_data", {})
    if not scraped_data_nested.get('zip_bytes'): raise dash.exceptions.PreventUpdate
    return dict(content=scraped_data_nested['zip_bytes'], filename=scraped_data_nested.get('zip_name', 'auto_scraped_pt_images.zip'), base64=True)

@app.callback(
    Output("download-auto-excel-gh", "data"),
    Input({'type': 'auto-download-btn', 'index': 'gh-excel'}, 'n_clicks'),
    State('active-gh-case-data-store', 'data'), 
    prevent_initial_call=True
)
def download_auto_gh_excel(n_clicks_dl, gh_case_data_from_store):
    if not n_clicks_dl or not gh_case_data_from_store: raise dash.exceptions.PreventUpdate
    scraped_data_nested = gh_case_data_from_store.get("scraped_files_data", {})
    if not scraped_data_nested.get('excel_bytes'): raise dash.exceptions.PreventUpdate
    return dict(content=scraped_data_nested['excel_bytes'], filename=scraped_data_nested.get('excel_name', 'auto_scraped_gh.xlsx'), base64=True)

@app.callback(
    Output("download-auto-zip-gh", "data"),
    Input({'type': 'auto-download-btn', 'index': 'gh-zip'}, 'n_clicks'),
    State('active-gh-case-data-store', 'data'), 
    prevent_initial_call=True
)
def download_auto_gh_zip(n_clicks_dl, gh_case_data_from_store):
    if not n_clicks_dl or not gh_case_data_from_store: raise dash.exceptions.PreventUpdate
    scraped_data_nested = gh_case_data_from_store.get("scraped_files_data", {})
    if not scraped_data_nested.get('zip_bytes'): raise dash.exceptions.PreventUpdate
    return dict(content=scraped_data_nested['zip_bytes'], filename=scraped_data_nested.get('zip_name', 'auto_scraped_gh_images.zip'), base64=True)

# --- WEB SCRAPER CALLBACKS ---
@app.callback(
    [Output('scraper-status-placeholder', 'children'),
     Output('web-scraper-output-store', 'data'),
     Output('scraper-download-excel-button', 'style'),
     Output('scraper-download-zip-button', 'style'),
     Output('processing-flags-store', 'data', allow_duplicate=True)],
    [Input('scraper-start-button', 'n_clicks')],
    [State('scraper-url-input', 'value'),
     State('scraper-country-dropdown', 'value'),
     State('processing-flags-store', 'data')],
    prevent_initial_call=True
)
def run_web_scraper_callback(n_clicks_scrape, url, selected_country_scrape, current_processing_flags):
    global ffmpeg_path_global, IMAGES_OUTPUT_FOLDER 

    ctx = dash.callback_context
    if not n_clicks_scrape or not ctx.triggered or ctx.triggered[0]['prop_id'].split('.')[0] != 'scraper-start-button':
        return dash.no_update, dash.no_update, dash.no_update, dash.no_update, dash.no_update

    hidden_button_style_dict = {**button_style, 'display': 'none'}
    visible_button_style_dict = {**button_style, 'display': 'inline-block', 'marginRight':'5px'}
    
    if current_processing_flags.get('scraping') or \
       current_processing_flags.get('local_processing') or \
       current_processing_flags.get('pdf_processing'):
        return html.P("Another data processing operation (scrape, local, or PDF) is already in progress. Please wait.", style={'color': 'orange'}), \
               dash.no_update, hidden_button_style_dict, hidden_button_style_dict, dash.no_update

    if not url or not url.startswith(('http:', 'https:')):
        return html.P("Please enter a valid URL (starting with http: or https:).", style={'color': 'red'}), \
               dash.no_update, hidden_button_style_dict, hidden_button_style_dict, dash.no_update

    updated_flags = current_processing_flags.copy()
    updated_flags['scraping'] = True
    
    scraper_output_data = {'timestamp': None, 'excel_bytes': None, 'excel_name': None, 'zip_bytes': None, 'zip_name': None}
    excel_style_to_set = hidden_button_style_dict
    zip_style_to_set = hidden_button_style_dict
    status_message_content = "Starting web scraping... This may take some moments. Please wait."
    status_message = html.P(status_message_content, style={'color': 'lightblue'})

    try:
        add_log(f"Web Scraper: Starting for URL: {url}, Country: {selected_country_scrape}", "info")
        if not ffmpeg_path_global: find_ffmpeg_on_startup() 
        
        menu_data = scrape_website(url, ffmpeg_path_global) 
        if not menu_data:
            status_message = html.P(f"No data scraped from {url}. Check logs for details.", style={'color': 'orange'})
        else:
            add_log(f"Web Scraper: Scraped {len(menu_data)} items. Processing images and data...", "info")
            df_processed, images_saved = process_web_images_and_data(menu_data, url, ffmpeg_path_global) 
            
            if df_processed is None or df_processed.empty:
                status_message = html.P("Web scraping data processing failed or yielded no data. Check logs.", style={'color': 'orange'})
            else:
                add_log(f"Web Scraper: Data processed ({df_processed.shape[0]} items). Creating output files...", "info")
                excel_bytes, excel_name, zip_bytes, zip_name = create_output_files(df_processed, images_saved, IMAGES_OUTPUT_FOLDER, selected_country_scrape) 
                
                scraper_output_data['timestamp'] = time.time()
                files_generated = False
                if excel_bytes:
                    scraper_output_data['excel_bytes'] = base64.b64encode(excel_bytes).decode()
                    scraper_output_data['excel_name'] = excel_name
                    excel_style_to_set = visible_button_style_dict
                    files_generated = True
                if zip_bytes:
                    scraper_output_data['zip_bytes'] = base64.b64encode(zip_bytes).decode()
                    scraper_output_data['zip_name'] = zip_name
                    zip_style_to_set = visible_button_style_dict
                    files_generated = True
                
                status_message = html.P("Scraping & processing complete. Files ready." if files_generated else "Scraping complete, but no output files generated. Check logs.", 
                                        style={'color': 'green' if files_generated else 'orange'})
    except Exception as e_scraper:
        detailed_error_msg = traceback.format_exc()
        add_log(f"Web Scraper: CRITICAL ERROR for '{url}': {e_scraper}\n{detailed_error_msg}", "error")
        status_message = html.Div([
            html.P("An error occurred during web scraping:", style={'color': 'red', 'fontWeight': 'bold'}),
            html.Pre(f"{str(e_scraper)}\nSee server logs for more details.", 
                     style={'color': 'red', 'border': '1px solid red', 'padding': '5px', 
                            'maxHeight': '100px', 'overflowY': 'auto', 'whiteSpace': 'pre-wrap'})
        ])
    finally:
        updated_flags['scraping'] = False
    
    return status_message, scraper_output_data, excel_style_to_set, zip_style_to_set, updated_flags

@app.callback(
    Output("download-excel-web", "data"), 
    Input("scraper-download-excel-button", "n_clicks"), 
    State("web-scraper-output-store", "data"), 
    prevent_initial_call=True
)
def download_web_excel_callback(n_clicks_dl_excel, web_store_data):
    if not n_clicks_dl_excel or not web_store_data or not web_store_data.get('excel_bytes'):
        raise dash.exceptions.PreventUpdate
    return dict(content=web_store_data['excel_bytes'], filename=web_store_data.get('excel_name', 'scraped_data.xlsx'), base64=True)

@app.callback(
    Output("download-zip-web", "data"), 
    Input("scraper-download-zip-button", "n_clicks"), 
    State("web-scraper-output-store", "data"), 
    prevent_initial_call=True
)
def download_web_zip_callback(n_clicks_dl_zip, web_store_data):
    if not n_clicks_dl_zip or not web_store_data or not web_store_data.get('zip_bytes'):
        raise dash.exceptions.PreventUpdate
    return dict(content=web_store_data['zip_bytes'], filename=web_store_data.get('zip_name', 'scraped_images.zip'), base64=True)

# --- LOCAL IMAGE PROCESSING CALLBACKS ---
@app.callback(
    [Output('local-image-upload-status', 'children'),
     Output('uploaded-local-images-store', 'data')],
    [Input('local-image-uploader', 'contents')],
    [State('local-image-uploader', 'filename'),
     State('local-image-uploader', 'last_modified')],
    prevent_initial_call=True
)
def update_local_image_upload_list(list_of_image_contents, list_of_image_names, list_of_image_dates):
    if list_of_image_contents is not None:
        new_image_files_data = [{'filename': n, 'last_modified': d, 'content': c} 
                              for c, n, d in zip(list_of_image_contents, list_of_image_names, list_of_image_dates)]
        status_message_display = html.Div([
            html.P(f"{len(new_image_files_data)} image(s) selected:"),
            html.Ul([html.Li(data['filename']) for data in new_image_files_data], style={'maxHeight':'100px', 'overflowY':'auto'})
        ])
        return status_message_display, new_image_files_data
    return html.P("Drag and drop or select local images to process."), []

@app.callback(
    [Output('local-image-status-placeholder', 'children'),
     Output('local-image-output-store', 'data'),
     Output('local-image-download-zip-button', 'style'),
     Output('processing-flags-store', 'data', allow_duplicate=True)],
    [Input('local-image-process-button', 'n_clicks')],
    [State('uploaded-local-images-store', 'data'),
     State('processing-flags-store', 'data')],
    prevent_initial_call=True
)
def process_local_images_callback(n_clicks_process_local, local_uploaded_files_data, current_processing_flags):
    global ffmpeg_path_global, LOCAL_IMAGES_OUTPUT_FOLDER 

    ctx = dash.callback_context
    if not n_clicks_process_local or not ctx.triggered or ctx.triggered[0]['prop_id'].split('.')[0] != 'local-image-process-button':
        return dash.no_update, dash.no_update, dash.no_update, dash.no_update

    hidden_btn_style = {**button_style, 'display': 'none'}
    visible_btn_style = {**button_style, 'display': 'inline-block'}
    
    if current_processing_flags.get('scraping') or \
       current_processing_flags.get('local_processing') or \
       current_processing_flags.get('pdf_processing'):
        return html.P("Another data processing operation (scrape, local, or PDF) is active. Please wait.", style={'color': 'orange'}), dash.no_update, hidden_btn_style, dash.no_update
    if not local_uploaded_files_data:
        return html.P("No images uploaded to process.", style={'color': 'red'}), dash.no_update, hidden_btn_style, dash.no_update

    updated_flags = current_processing_flags.copy()
    updated_flags['local_processing'] = True
    output_store_data_local_img = {'timestamp': None, 'zip_bytes': None, 'zip_name': None}
    zip_style_local_img = hidden_btn_style
    status_msg_local_img = html.P("Processing local images...", style={'color': 'lightblue'})
    processed_image_paths_local = []

    try:
        add_log(f"Local Img Proc: Starting for {len(local_uploaded_files_data)} files.", "info")
        if not ffmpeg_path_global: find_ffmpeg_on_startup() 
        if not os.path.exists(LOCAL_IMAGES_OUTPUT_FOLDER): os.makedirs(LOCAL_IMAGES_OUTPUT_FOLDER)

        for i, file_data_item in enumerate(local_uploaded_files_data):
            content_type_local, content_string_local = file_data_item['content'].split(',')
            img_bytes_local = base64.b64decode(content_string_local)
            base_name_local = sanitize_filename(f"{i}_{os.path.splitext(file_data_item['filename'])[0]}") 
            path_local = process_single_image(img_bytes_local, base_name_local, LOCAL_IMAGES_OUTPUT_FOLDER, ffmpeg_path_global) 
            
            if path_local and path_local != "FFmpeg required": 
                processed_image_paths_local.append(path_local)
            elif path_local == "FFmpeg required": 
                add_log(f"FFmpeg needed for local image {file_data_item['filename']}, but conversion failed or FFmpeg not found.", "warning")
            else: 
                add_log(f"Failed to process local image: {file_data_item['filename']}", "warning")
        
        if processed_image_paths_local:
            zip_buffer_local = io.BytesIO()
            zip_filename_local = f"processed_local_images_{time.strftime('%Y%m%d%H%M%S')}.zip"
            with zipfile.ZipFile(zip_buffer_local, 'w', zipfile.ZIP_DEFLATED) as zf_local:
                for p_local in processed_image_paths_local: zf_local.write(p_local, arcname=os.path.basename(p_local))
            
            output_store_data_local_img.update({
                'timestamp': time.time(),
                'zip_bytes': base64.b64encode(zip_buffer_local.getvalue()).decode(),
                'zip_name': zip_filename_local
            })
            zip_style_local_img = visible_btn_style
            status_msg_local_img = html.P(f"Processed {len(processed_image_paths_local)} images. ZIP ready.", style={'color': 'green'})
            add_log(f"Local Img Proc: ZIP '{zip_filename_local}' ready with {len(processed_image_paths_local)} images.", "success")
        else:
            status_msg_local_img = html.P("No images were successfully processed from the upload.", style={'color': 'orange'})
            add_log("Local Img Proc: No images successfully processed.", "warning")
            
    except Exception as e_local_img:
        detailed_error_local_img = traceback.format_exc()
        add_log(f"Local Img Proc: CRITICAL ERROR: {e_local_img}\n{detailed_error_local_img}", "error")
        status_msg_local_img = html.P(f"Error processing local images: {e_local_img}", style={'color': 'red'})
    finally:
        updated_flags['local_processing'] = False
        
    return status_msg_local_img, output_store_data_local_img, zip_style_local_img, updated_flags

@app.callback(
    Output("download-zip-local", "data"), 
    Input("local-image-download-zip-button", "n_clicks"), 
    State("local-image-output-store", "data"), 
    prevent_initial_call=True
)
def download_local_images_zip_callback(n_clicks_dl_local_zip, local_img_store_data):
    if not n_clicks_dl_local_zip or not local_img_store_data or not local_img_store_data.get('zip_bytes'):
        raise dash.exceptions.PreventUpdate
    return dict(content=local_img_store_data['zip_bytes'], filename=local_img_store_data.get('zip_name', 'local_images.zip'), base64=True)

# --- PDF PROCESSING CALLBACKS ---
@app.callback(
    [Output('pdf-upload-status', 'children'),
     Output('uploaded-pdf-files-store', 'data')],
    [Input('pdf-file-uploader', 'contents')],
    [State('pdf-file-uploader', 'filename'),
     State('pdf-file-uploader', 'last_modified')],
    prevent_initial_call=True
)
def update_pdf_upload_list(list_of_pdf_contents, list_of_pdf_names, list_of_pdf_dates):
    if list_of_pdf_contents is not None:
        new_pdf_files_data = [{'filename': n, 'last_modified': d, 'content': c} 
                             for c, n, d in zip(list_of_pdf_contents, list_of_pdf_names, list_of_pdf_dates)]
        status_message_pdf_upload = html.Div([
            html.P(f"{len(new_pdf_files_data)} PDF(s) selected:"),
            html.Ul([html.Li(data['filename']) for data in new_pdf_files_data], style={'maxHeight':'100px', 'overflowY':'auto'})
        ])
        return status_message_pdf_upload, new_pdf_files_data
    return html.P("Drag and drop or select PDF files to process."), []

class MockUploadedFile: 
    def __init__(self, name, content_bytes):
        self.name = name
        self._content_bytes = content_bytes
    def getvalue(self):
        return self._content_bytes

@app.callback(
    [Output('pdf-status-placeholder', 'children'),
     Output('pdf-output-store', 'data'),
     Output('pdf-download-excel-button', 'style'),
     Output('pdf-download-zip-button', 'style'),
     Output('processing-flags-store', 'data', allow_duplicate=True)],
    [Input('pdf-process-button', 'n_clicks')],
    [State('uploaded-pdf-files-store', 'data'),
     State('pdf-country-dropdown', 'value'),
     State('processing-flags-store', 'data')],
    prevent_initial_call=True
)
def process_pdf_files_callback(n_clicks_process_pdf, pdf_uploaded_store_data, selected_country_for_pdf, current_processing_flags):
    global ffmpeg_path_global, PDF_IMAGES_OUTPUT_FOLDER 

    ctx = dash.callback_context
    if not n_clicks_process_pdf or not ctx.triggered or ctx.triggered[0]['prop_id'].split('.')[0] != 'pdf-process-button':
        return dash.no_update, dash.no_update, dash.no_update, dash.no_update, dash.no_update

    hidden_btn_style = {**button_style, 'display': 'none'}
    visible_btn_style = {**button_style, 'display': 'inline-block', 'marginRight':'5px'}
    
    if current_processing_flags.get('scraping') or \
       current_processing_flags.get('local_processing') or \
       current_processing_flags.get('pdf_processing'):
        return html.P("Another data processing operation (scrape, local, or PDF) is active. Please wait.", style={'color': 'orange'}), dash.no_update, hidden_btn_style, hidden_btn_style, dash.no_update
    if not pdf_uploaded_store_data:
        return html.P("No PDF files uploaded to process.", style={'color': 'red'}), dash.no_update, hidden_btn_style, hidden_btn_style, dash.no_update

    updated_flags = current_processing_flags.copy()
    updated_flags['pdf_processing'] = True
    output_store_data_pdf = {'timestamp': None, 'excel_bytes': None, 'excel_name': None, 'zip_bytes': None, 'zip_name': None}
    excel_style_pdf = hidden_btn_style
    zip_style_pdf = hidden_btn_style
    status_msg_pdf = html.P("Processing PDF files...", style={'color': 'lightblue'})
    
    mock_pdf_files_for_processing = []
    for file_data_pdf in pdf_uploaded_store_data:
        try:
            content_string_pdf = file_data_pdf['content'].split(',')[1]
            pdf_bytes_content = base64.b64decode(content_string_pdf)
            mock_pdf_files_for_processing.append(MockUploadedFile(file_data_pdf['filename'], pdf_bytes_content))
        except Exception as e_b64_decode_pdf:
            add_log(f"PDF Proc: Error decoding base64 content for {file_data_pdf['filename']}: {e_b64_decode_pdf}", "error")
    
    if not mock_pdf_files_for_processing:
         status_msg_pdf = html.P("No valid PDF content found in uploaded files after attempting to decode.", style={'color': 'red'})
         updated_flags['pdf_processing'] = False
         return status_msg_pdf, output_store_data_pdf, excel_style_pdf, zip_style_pdf, updated_flags

    try:
        add_log(f"PDF Proc: Starting for {len(mock_pdf_files_for_processing)} files, Country output format: {selected_country_for_pdf}", "info")
        if not ffmpeg_path_global: find_ffmpeg_on_startup() 
        
        df_pdf_data_processed, all_pdf_extracted_image_paths = process_extracted_pdf_data(mock_pdf_files_for_processing, selected_country_for_pdf) 

        if df_pdf_data_processed is None or df_pdf_data_processed.empty:
            status_msg_pdf = html.P("PDF processing failed or yielded no item data. Check logs.", style={'color': 'orange'})
            add_log("PDF Proc: df_pdf_data_processed is None or empty after extraction.", "warning")
        else:
            add_log(f"PDF Proc: Data extracted ({df_pdf_data_processed.shape[0]} items). Creating output files...", "info")
            excel_bytes_pdf, excel_name_pdf, zip_bytes_pdf, zip_name_pdf = create_output_files( 
                df_pdf_data_processed, all_pdf_extracted_image_paths, PDF_IMAGES_OUTPUT_FOLDER, selected_country_for_pdf
            )
            
            output_store_data_pdf['timestamp'] = time.time()
            files_generated_pdf = False
            if excel_bytes_pdf:
                output_store_data_pdf.update({'excel_bytes': base64.b64encode(excel_bytes_pdf).decode(), 'excel_name': excel_name_pdf})
                excel_style_pdf = visible_btn_style
                files_generated_pdf = True
            if zip_bytes_pdf and all_pdf_extracted_image_paths:
                output_store_data_pdf.update({'zip_bytes': base64.b64encode(zip_bytes_pdf).decode(), 'zip_name': zip_name_pdf})
                zip_style_pdf = visible_btn_style
                files_generated_pdf = True
            
            status_msg_pdf = html.P("PDF processing complete. Files ready." if files_generated_pdf else 
                                   "PDF processing done, but no files to download (or no images to zip).", 
                                   style={'color': 'green' if files_generated_pdf else 'orange'})
            add_log(f"PDF Proc: Complete. Excel: {'Yes' if excel_bytes_pdf else 'No'}, Images ZIP: {'Yes' if zip_bytes_pdf and all_pdf_extracted_image_paths else 'No'}", "info")

    except Exception as e_pdf_proc_main:
        detailed_error_pdf_main = traceback.format_exc()
        add_log(f"PDF Proc: CRITICAL ERROR: {e_pdf_proc_main}\n{detailed_error_pdf_main}", "error")
        status_msg_pdf = html.P(f"Error processing PDFs: {e_pdf_proc_main}", style={'color': 'red'})
    finally:
        updated_flags['pdf_processing'] = False
        
    return status_msg_pdf, output_store_data_pdf, excel_style_pdf, zip_style_pdf, updated_flags

@app.callback(
    Output("download-excel-pdf", "data"), 
    Input("pdf-download-excel-button", "n_clicks"), 
    State("pdf-output-store", "data"), 
    prevent_initial_call=True
)
def download_pdf_excel_callback(n_clicks_dl_pdf_excel, pdf_store_data_dl):
    if not n_clicks_dl_pdf_excel or not pdf_store_data_dl or not pdf_store_data_dl.get('excel_bytes'):
        raise dash.exceptions.PreventUpdate
    return dict(content=pdf_store_data_dl['excel_bytes'], filename=pdf_store_data_dl.get('excel_name', 'pdf_extracted_data.xlsx'), base64=True)

@app.callback(
    Output("download-zip-pdf", "data"), 
    Input("pdf-download-zip-button", "n_clicks"), 
    State("pdf-output-store", "data"), 
    prevent_initial_call=True
)
def download_pdf_images_zip_callback(n_clicks_dl_pdf_zip, pdf_store_data_zip):
    if not n_clicks_dl_pdf_zip or not pdf_store_data_zip or not pdf_store_data_zip.get('zip_bytes'):
        raise dash.exceptions.PreventUpdate
    return dict(content=pdf_store_data_zip['zip_bytes'], filename=pdf_store_data_zip.get('zip_name', 'pdf_extracted_images.zip'), base64=True)


# --- UPDATED CALLBACK FOR DAILY LOG AND LEADERBOARDS (Bot, Daily, Monthly) ---
@app.callback(
    [Output('bot-activity-table-div', 'children'),
     # **MODIFIED Outputs for daily leaderboard table**
     Output('daily-leaderboard-table', 'data'),
     Output('daily-leaderboard-table', 'columns'),
     Output('daily-leaderboard-status-message', 'children'), # For messages like "No data"
     Output('daily-leaderboard-case-details-div', 'children'),
     Output('monthly-leaderboard-table-div', 'children'), 
     Output('sidebar-data-store', 'data')],
    [Input('load-log-button', 'n_clicks'),
     Input('load-monthly-leaderboard-button', 'n_clicks'),
     Input('daily-leaderboard-table', 'active_cell')], 
    [State('log-date-picker', 'date'),
     State('month-picker', 'value'),
     State('year-picker', 'value'),
     State('daily-leaderboard-table', 'data'), 
     State('sidebar-data-store', 'data')],
    prevent_initial_call=True
)
def update_sidebar_reports(
    n_clicks_daily, n_clicks_monthly, active_cell_daily,
    selected_date_str, selected_month, selected_year,
    daily_leaderboard_current_data, current_sidebar_data 
):
    ctx = dash.callback_context
    triggered_id = ctx.triggered[0]['prop_id'].split('.')[0] if ctx.triggered else None

    # Initialize outputs
    bot_table_component = dash.no_update
    daily_lb_data_out = dash.no_update
    daily_lb_columns_out = dash.no_update
    daily_lb_status_msg_out = dash.no_update # For messages related to daily leaderboard
    daily_case_details_component = dash.no_update
    monthly_leaderboard_component = dash.no_update # This will hold the full DataTable or a message
    
    sidebar_store_output = current_sidebar_data if current_sidebar_data else \
                           {'timestamp': None, 'bot_log_data': None, 'leaderboard_data': None, 
                            'monthly_leaderboard_data': None, 'daily_leaderboard_case_details_log': None}
    if triggered_id: 
        sidebar_store_output['timestamp'] = time.time()

    # Default columns for an empty daily leaderboard table
    default_daily_lb_columns = [{'name':'Assigned User', 'id':'Assigned User'}, {'name':'Cases to InProgress', 'id':'Cases to InProgress'}]


    if triggered_id == 'load-log-button' and n_clicks_daily:
        add_log(f"Sidebar: 'Load Daily Activity' clicked. Date: {selected_date_str}", "info")
        daily_case_details_component = html.Div() # Clear details when new date is loaded

        if not selected_date_str:
            error_msg = html.P("Please select a date for daily activity.", style={'color':'red'})
            # Update daily leaderboard outputs to show empty table and message
            return error_msg, [], default_daily_lb_columns, error_msg, html.Div(), dash.no_update, sidebar_store_output

        try:
            df_log_full = get_case_log_df() 
            if df_log_full.empty:
                error_msg = html.P("Case activity log file is empty.", style={'color':'orange'})
                return error_msg, [], default_daily_lb_columns, error_msg, html.Div(), dash.no_update, sidebar_store_output

            df_proc_daily = df_log_full.copy()
            if 'Date' not in df_proc_daily.columns:
                error_msg = html.P("Error: 'Date' column missing in log.", style={'color':'red'})
                return error_msg, [], default_daily_lb_columns, error_msg, html.Div(), dash.no_update, sidebar_store_output
            
            df_proc_daily['Date_dt'] = pd.to_datetime(df_proc_daily['Date'], errors='coerce').dt.date
            selected_dt_obj = pd.to_datetime(selected_date_str).date()
            df_filtered_for_day = df_proc_daily[df_proc_daily['Date_dt'] == selected_dt_obj].copy()

            if df_filtered_for_day.empty:
                no_activity_msg = html.P(f"No activity found for {selected_date_str}.", style={'color':'orange'})
                bot_table_component = no_activity_msg
                daily_lb_data_out = []
                daily_lb_columns_out = default_daily_lb_columns
                daily_lb_status_msg_out = no_activity_msg
                sidebar_store_output['bot_log_data'] = None
                sidebar_store_output['leaderboard_data'] = None 
                sidebar_store_output['daily_leaderboard_case_details_log'] = None
            else:
                # Bot Activity
                bot_user_id = "BOT_CLAIMED" 
                df_bot_activity_day = df_filtered_for_day[df_filtered_for_day['Assigned User'].astype(str).str.contains(bot_user_id, na=False, case=False)]
                if not df_bot_activity_day.empty:
                    bot_cols = ['Observed Timestamp', 'Case Display ID', 'Country', 'Status (Observed)', 'Account Name', 'Duration (HH:MM:SS)']
                    bot_cols_exist = [c for c in bot_cols if c in df_bot_activity_day.columns]
                    bot_df_display = df_bot_activity_day[bot_cols_exist].fillna("N/A")
                    bot_table_component = dash_table.DataTable(
                        columns=[{"name": i, "id": i} for i in bot_df_display.columns], data=bot_df_display.to_dict('records'),
                        style_cell={'textAlign': 'left', 'backgroundColor': '#252526', 'color': '#E0E0E0', 'border': '1px solid #3E3E3E', 'fontSize': '11px', 'whiteSpace': 'normal', 'height': 'auto', 'minWidth': '50px', 'maxWidth': '130px', 'overflow': 'hidden', 'textOverflow': 'ellipsis'},
                        style_header={'backgroundColor': '#4CAF50', 'fontWeight': 'bold', 'color': 'white'}, page_size=5, sort_action="native"
                    )
                    sidebar_store_output['bot_log_data'] = bot_df_display.to_dict('records')
                else:
                    bot_table_component = html.P(f"No bot activity for {selected_date_str}.")

                # Daily Team Leaderboard
                obs_ts_col, case_id_col, status_col, user_col = 'Observed Timestamp', 'Case Display ID', 'Status (Observed)', 'Assigned User'
                req_cols = [obs_ts_col, case_id_col, status_col, user_col]

                if not all(col in df_filtered_for_day.columns for col in req_cols):
                    daily_lb_status_msg_out = html.P(f"Leaderboard error: Missing columns on {selected_date_str}.", style={'color':'red'})
                    daily_lb_data_out = []
                    daily_lb_columns_out = default_daily_lb_columns
                    sidebar_store_output['leaderboard_data'] = None
                    sidebar_store_output['daily_leaderboard_case_details_log'] = None
                else:
                    df_day_lb = df_filtered_for_day.copy() 
                    try: 
                        df_day_lb[obs_ts_col] = pd.to_datetime(df_day_lb[obs_ts_col], errors='coerce')
                    except Exception as e_ts_daily_lb_load_fix: 
                        add_log(f"Leaderboard (Daily Load): Warning converting '{obs_ts_col}': {e_ts_daily_lb_load_fix}", "warning")
                    
                    df_day_lb[case_id_col] = df_day_lb[case_id_col].astype(str)
                    df_day_lb[status_col] = df_day_lb[status_col].astype(str).str.strip().str.lower() 
                    df_day_lb[user_col] = df_day_lb[user_col].astype(str).str.strip()

                    if pd.api.types.is_datetime64_any_dtype(df_day_lb[obs_ts_col]) and not df_day_lb[obs_ts_col].isnull().all():
                        df_day_lb.sort_values(by=[case_id_col, obs_ts_col], inplace=True, na_position='first')
                    else:
                        df_day_lb.sort_values(by=[case_id_col], inplace=True, na_position='first')
                    
                    user_scores_day = {}
                    counted_case_ids_day = set()
                    daily_leaderboard_details_for_store = {} 

                    for _, row in df_day_lb.iterrows():
                        case_id = row[case_id_col]
                        status = row[status_col]
                        user = row[user_col]
                        is_bot = bot_user_id.lower() in user.lower() if user else True
                        if not user or user.lower() == 'n/a' or user == "" or is_bot: continue

                        if status == "inprogress" and case_id not in counted_case_ids_day:
                            user_scores_day[user] = user_scores_day.get(user, 0) + 1
                            counted_case_ids_day.add(case_id)
                            if user not in daily_leaderboard_details_for_store:
                                daily_leaderboard_details_for_store[user] = []
                            daily_leaderboard_details_for_store[user].append(case_id)
                    
                    sidebar_store_output['daily_leaderboard_case_details_log'] = daily_leaderboard_details_for_store

                    if user_scores_day:
                        lb_df_day = pd.DataFrame(list(user_scores_day.items()), columns=['Assigned User', 'Cases to InProgress'])
                        lb_df_day.sort_values(by='Cases to InProgress', ascending=False, inplace=True)
                        
                        daily_lb_data_out = lb_df_day.to_dict('records')
                        daily_lb_columns_out = [{"name": i, "id": i} for i in lb_df_day.columns]
                        daily_lb_status_msg_out = None 
                        sidebar_store_output['leaderboard_data'] = lb_df_day.to_dict('records')
                    else:
                        daily_lb_data_out = []
                        daily_lb_columns_out = default_daily_lb_columns
                        daily_lb_status_msg_out = html.P(f"No 'InProgress' transitions for users on {selected_date_str}.")
                        sidebar_store_output['leaderboard_data'] = None
        except Exception as e_daily:
            error_msg_daily_text = f"Error loading daily log for {selected_date_str}: {e_daily}"
            error_msg_daily_comp = html.P(error_msg_daily_text, style={'color':'red'})
            add_log(f"Sidebar: Error processing daily log: {e_daily}\n{traceback.format_exc()}", "error")
            bot_table_component = error_msg_daily_comp
            daily_lb_data_out = []
            daily_lb_columns_out = default_daily_lb_columns
            daily_lb_status_msg_out = error_msg_daily_comp
            daily_case_details_component = html.Div()
            sidebar_store_output['bot_log_data'] = None
            sidebar_store_output['leaderboard_data'] = None
            sidebar_store_output['daily_leaderboard_case_details_log'] = None
        
    elif triggered_id == 'daily-leaderboard-table' and active_cell_daily and daily_leaderboard_current_data: # daily_leaderboard_current_data is from State
        add_log(f"Sidebar: Daily leaderboard cell clicked: {active_cell_daily}", "debug")
        clicked_row_index = active_cell_daily['row']
        date_for_details_str = selected_date_str 
        
        if daily_leaderboard_current_data and isinstance(daily_leaderboard_current_data, list) and clicked_row_index < len(daily_leaderboard_current_data):
            clicked_user = daily_leaderboard_current_data[clicked_row_index].get('Assigned User')
            if clicked_user:
                stored_case_details = current_sidebar_data.get('daily_leaderboard_case_details_log', {}) if current_sidebar_data else {}
                user_case_ids = stored_case_details.get(clicked_user, [])
                
                if user_case_ids:
                    daily_case_details_component = html.Div([
                        html.P(f"Cases for {clicked_user} (on {date_for_details_str} that went 'InProgress'):", style={'fontWeight':'bold', 'marginTop':'10px'}),
                        dcc.Dropdown(
                            options=[{'label': cid, 'value': cid} for cid in sorted(list(set(user_case_ids)))],
                            placeholder="Affected Case IDs", clearable=True, multi=True,
                            style={'color':'#333', 'marginTop':'5px', 'backgroundColor':'#252526', 'width':'100%'}
                        )
                    ])
                else:
                    daily_case_details_component = html.P(f"No specific Case IDs found for {clicked_user} on {date_for_details_str}.", style={'color':'orange', 'marginTop':'10px'})
            else:
                daily_case_details_component = html.P("Could not identify clicked user from table.", style={'color':'orange', 'marginTop':'10px'})
        else:
            daily_case_details_component = html.Div() 
            add_log(f"Sidebar: Clicked on daily leaderboard, but data was invalid or index out of bounds. Row: {clicked_row_index}", "debug")

    elif triggered_id == 'load-monthly-leaderboard-button' and n_clicks_monthly:
        add_log(f"Sidebar: 'Load Monthly Leaderboard' clicked. Month: {selected_month}, Year: {selected_year}", "info")
        daily_case_details_component = html.Div() # Clear daily details

        if not selected_month or not selected_year:
            monthly_leaderboard_component = html.P("Please select both month and year.", style={'color':'red'})
        else:
            try:
                df_log_full_monthly = get_case_log_df()
                if df_log_full_monthly.empty:
                    monthly_leaderboard_component = html.P("Case activity log is empty.", style={'color':'orange'})
                else:
                    df_proc_monthly = df_log_full_monthly.copy()
                    if 'Date' not in df_proc_monthly.columns:
                         monthly_leaderboard_component = html.P("Error: 'Date' column missing in log.", style={'color':'red'})
                    else:
                        df_proc_monthly['Date_dt'] = pd.to_datetime(df_proc_monthly['Date'], errors='coerce')
                        df_filtered_for_month = df_proc_monthly[
                            (df_proc_monthly['Date_dt'].dt.month == int(selected_month)) &
                            (df_proc_monthly['Date_dt'].dt.year == int(selected_year))
                        ].copy()

                        if df_filtered_for_month.empty:
                            month_name = datetime(2000,int(selected_month),1).strftime('%B') if selected_month else "Selected Month"
                            monthly_leaderboard_component = html.P(f"No activity found for {month_name} {selected_year}.", style={'color':'orange'})
                            sidebar_store_output['monthly_leaderboard_data'] = None
                        else:
                            obs_ts_col, case_id_col, status_col, user_col = 'Observed Timestamp', 'Case Display ID', 'Status (Observed)', 'Assigned User'
                            req_cols_monthly = [obs_ts_col, case_id_col, status_col, user_col]
                            if not all(col in df_filtered_for_month.columns for col in req_cols_monthly):
                                monthly_leaderboard_component = html.P(f"Monthly Leaderboard error: Missing columns.", style={'color':'red'})
                            else:
                                try: 
                                    df_filtered_for_month[obs_ts_col] = pd.to_datetime(df_filtered_for_month[obs_ts_col], errors='coerce')
                                except Exception as e_ts_monthly_load_fix: 
                                    add_log(f"Leaderboard (Monthly Load): Warning converting '{obs_ts_col}': {e_ts_monthly_load_fix}", "warning")

                                df_filtered_for_month[case_id_col] = df_filtered_for_month[case_id_col].astype(str)
                                df_filtered_for_month[status_col] = df_filtered_for_month[status_col].astype(str).str.strip().str.lower() # Corrected typo
                                df_filtered_for_month[user_col] = df_filtered_for_month[user_col].astype(str).str.strip()

                                if pd.api.types.is_datetime64_any_dtype(df_filtered_for_month[obs_ts_col]) and not df_filtered_for_month[obs_ts_col].isnull().all():
                                     df_filtered_for_month.sort_values(by=[case_id_col, obs_ts_col], inplace=True, na_position='first')
                                else:
                                     df_filtered_for_month.sort_values(by=[case_id_col], inplace=True, na_position='first')

                                user_scores_month = {}
                                counted_case_ids_month = set()
                                bot_user_id = "BOT_CLAIMED"

                                for _, row in df_filtered_for_month.iterrows():
                                    case_id = row[case_id_col]
                                    status = row[status_col]
                                    user = row[user_col]
                                    is_bot = bot_user_id.lower() in user.lower() if user else True
                                    if not user or user.lower() == 'n/a' or user == "" or is_bot: continue

                                    if status == "inprogress" and case_id not in counted_case_ids_month:
                                        user_scores_month[user] = user_scores_month.get(user, 0) + 1
                                        counted_case_ids_month.add(case_id)
                                
                                if user_scores_month:
                                    lb_df_month = pd.DataFrame(list(user_scores_month.items()), columns=['Assigned User', 'Cases to InProgress'])
                                    lb_df_month.sort_values(by='Cases to InProgress', ascending=False, inplace=True)
                                    monthly_leaderboard_component = dash_table.DataTable(
                                        columns=[{"name": i, "id": i} for i in lb_df_month.columns], data=lb_df_month.to_dict('records'),
                                        style_cell={'textAlign': 'left', 'backgroundColor': '#252526', 'color': '#E0E0E0', 'border': '1px solid #3E3E3E', 'fontSize': '12px'},
                                        style_header={'backgroundColor': '#007BFF', 'fontWeight': 'bold', 'color': 'white'}, page_size=10, sort_action="native"
                                    )
                                    sidebar_store_output['monthly_leaderboard_data'] = lb_df_month.to_dict('records')
                                else:
                                    month_name_disp = datetime(2000,int(selected_month),1).strftime('%B') if selected_month else "Selected Month"
                                    monthly_leaderboard_component = html.P(f"No 'InProgress' transitions for users in {month_name_disp} {selected_year}.")
                                    sidebar_store_output['monthly_leaderboard_data'] = None
            except Exception as e_monthly:
                monthly_leaderboard_component = html.P(f"Error loading monthly leaderboard: {e_monthly}", style={'color':'red'})
                add_log(f"Sidebar: Error processing monthly leaderboard: {e_monthly}\n{traceback.format_exc()}", "error")
                sidebar_store_output['monthly_leaderboard_data'] = None
    else:
        pass

    return (
        bot_table_component, 
        daily_lb_data_out,                 # For daily-leaderboard-table.data
        daily_lb_columns_out,              # For daily-leaderboard-table.columns
        daily_lb_status_msg_out,           # For daily-leaderboard-status-message.children
        daily_case_details_component, 
        monthly_leaderboard_component, 
        sidebar_store_output
    )

# --- Application Entry Point ---
if __name__ == '__main__':
    add_log("Application (Dash) starting...", "info")
    find_ffmpeg_on_startup() 
    add_log(f"FFmpeg Path (Global): {ffmpeg_path_global if 'ffmpeg_path_global' in globals() else 'Not Set'}", "info")
    get_case_log_df() 
    app.run(debug=True, host='0.0.0.0', port=8050)




