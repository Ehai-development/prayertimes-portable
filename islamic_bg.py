"""
Prayer Times Display - Building from Scratch
Step 1: Islamic Background Design
"""

import tkinter as tk
from tkinter import Canvas
from tkinter import messagebox
from tkinter import font as tkfont
import math
import csv
import json
import re
import sys
import socket
import time
from datetime import date, datetime, timedelta
from pathlib import Path
from PIL import Image, ImageTk, ImageDraw, ImageOps
import urllib.request
import urllib.parse
import threading
import random

try:
    from hijri_converter import Hijri, Gregorian
except ImportError:
    try:
        from hijridate import Hijri, Gregorian
    except ImportError:
        Hijri = None
        Gregorian = None

# TEST MODE: Set to True to simulate prayer time changes for testing
TEST_MODE = False
# TEST DATE: Set this to simulate a specific date (format: "2026-02-27")
# When TEST_MODE is True, the app will use this date instead of system date
TEST_DATE = "2026-03-05"  # Set to None to use system date, or a date string to mock - Ramadan test date
# TEST TIME: Set this to simulate a specific time (format: "HH:MM:SS" in 24-hour format, e.g., "19:58:00")
TEST_TIME = None  # Disabled for now - set to a time string like "06:28:30" to test countdown
ENABLE_PERF_TRACE = False

_single_instance_socket = None


def acquire_single_instance_lock():
    """Allow only one running instance of this app on the machine."""
    global _single_instance_socket
    try:
        _single_instance_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        _single_instance_socket.bind(('127.0.0.1', 47653))
        _single_instance_socket.listen(1)
        return True
    except OSError:
        return False


class IslamicBackground:
    def __init__(self, root):
        self.root = root
        self.root.title("Prayer Times Display")

        self.base_width = 1920
        self.base_height = 1080
        self.ui_scale = 1.0
        self.logo_image_size = None
        
        # Start sized to current display so layout calculations match target screen
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        self.root.geometry(f"{screen_w}x{screen_h}+0+0")
        
        # Make sure window is visible and on top
        self.root.deiconify()
        self.root.state('normal')
        self.root.lift()
        self.root.focus()
        self.root.attributes('-topmost', True)
        self.root.after(1200, lambda: self.root.attributes('-topmost', False))
        
        # Fullscreen configuration (always start fullscreen)
        self._enter_fullscreen()
        self.root.configure(bg='#2c1169')
        
        # Keyboard bindings
        self.root.bind('<Escape>', self._exit_fullscreen)
        self.root.bind('<F11>', self._toggle_fullscreen)
        self.root.bind('q', lambda e: self.root.quit())
        self.root.bind('Q', lambda e: self.root.quit())
        
        # Create the canvas for drawing
        self.canvas = Canvas(root, bg='#2c1169', highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # Force window update so canvas has correct dimensions
        self.root.update_idletasks()
        
        # Bind resize event
        self.canvas.bind('<Configure>', self.on_resize)

        # When the window is first mapped, enforce fullscreen again.
        self._mapped_fullscreen_fix_done = False
        self.root.bind('<Map>', self._on_window_mapped, add='+')

        # Startup visibility nudges (helps on multi-display/TV setups)
        self._startup_nudge_attempts = 0
        self.root.after(250, self._startup_visibility_nudge)
        
        # Track start time for TEST_MODE dynamic time advancement
        self.test_mode_start_time = datetime.now() if TEST_MODE and TEST_TIME else None
        self._test_mode_date_logged = False
        self._test_mode_time_error_logged = False
        self._test_mode_date_error_logged = False
        
        # Initialize tracking variables FIRST
        self.countdown_text_id = None
        self.current_time_text_id = None
        self.current_time_outline_ids = []
        self.logo_image_tk = None
        self.next_prayer_prefix_text_id = None
        self.next_prayer_name_text_id = None
        self.next_prayer_in_text_id = None
        self.next_prayer_panel_id = None
        self.next_prayer_panel_width = None
        self.next_prayer_panel_height = 72
        self.next_prayer_panel_radius = 18
        self.next_prayer_panel_padding_x = 36
        self.next_prayer_max_panel_width = None
        self.next_prayer_line_x = None
        self.next_prayer_line_y = None
        self.next_prayer_panel_bounds = None
        self.next_prayer_athan_time = None
        self.ui_font_family = 'Bahnschrift'
        self.next_prayer_line_font = tkfont.Font(family=self.ui_font_family, size=20, weight='bold')
        self.next_prayer_prefix_font = tkfont.Font(family=self.ui_font_family, size=18, weight='bold')
        self.next_prayer_countdown_fixed_width = self.next_prayer_line_font.measure('88:88:88')
        self.next_prayer_static_width = None
        self._next_prayer_last_text_parts = None
        self._next_prayer_last_widths = (0, 0, 0, 0)
        # Next-prayer slide transition state (clean rewrite)
        self._np_rtl = False           # currently displayed RTL mode
        self._np_anim_active = False   # animation in progress
        self._np_anim_start_mono = 0.0 # time.monotonic() when animation started
        self._np_anim_duration = 0.65  # seconds
        self._np_old_data = None       # data being exited {prefix,name,in_,countdown,rtl}
        self._np_new_data = None       # data being entered
        self._np_anim_ticker_id = None # after() ID for animation ticker
        self._np_initialized = False   # committed mode initialized from first live sample
        self.build_info_text_id = None
        self.build_info_text = self.get_build_info_text()
        self.last_rendered_current_prayer = None
        self._last_transition_redraw_at = None
        self._transition_redraw_pending = False
        self._is_full_redraw = False
        self.prayer_box_shape_ids = {}
        self.prayer_box_bounds = {}
        self.athan_callout_box_id = None
        self.athan_callout_text_id = None
        self.athan_callout_prayer = None
        self.countdown_x = None
        self.countdown_y = None
        self._resize_redraw_job = None
        self._perf_last_log = {}
        self._last_seen_date = self.get_current_date()
        self._date_rollover_refresh_in_progress = False
        self.lantern_pulse_cycle_seconds = 3.2
        self.lantern_pulse_tick_ms = 1500
        
        self.star_twinkle_cycle_seconds = 2.5
        self.star_twinkle_tick_ms = 500
        self.eid_firework_cycle_seconds = 2.2
        self.eid_balloon_cycle_seconds = 9.5
        self.eid_animation_tick_ms = 220
        # Keep Takbeer cycle checks lightweight to avoid unnecessary redraw pressure.
        self.arafah_takbeer_tick_ms = 1000
        self.arafah_takbeer_particles = []
        self.arafah_takbeer_max_particles = 18
        self.arafah_takbeer_lines = [
            'الله أكبر الله أكبر الله أكبر',
            'لَا إِلٰهَ إِلَّا اللَّه',
            'اللَّهُ أَكْبَرُ، اللَّهُ أَكْبَرُ، وَلِلَّهِ الْحَمْد',
        ]
        self.arafah_takbeer_shower_text = '\n\n'.join(self.arafah_takbeer_lines)
        self.arafah_takbeer_cycle_order = ['Fajr', 'Duhr', 'Asr', 'Maghrib']
        self.arafah_takbeer_display_seconds = 3
        self.arafah_takbeer_pause_seconds = 15
        self.arafah_takbeer_cycle_phase = 'show'
        self.arafah_takbeer_cycle_index = 0
        self.arafah_takbeer_cycle_started_mono = time.monotonic()
        self.arafah_takbeer_cycle_after_id = None
        self.arafah_takbeer_start_date = None
        self.arafah_takbeer_end_date = None
        self.show_arafah_takbeer_panel = True
        self.show_takbeer_shower = True
        self.takbeer_shower_tick_ms = 16
        self.takbeer_shower_last_tick_mono = None

        # Current prayer glow animation
        self.glow_tick_ms = 80
        self.glow_cycle_seconds = 5.0
        self._glow_phase = 0.0  # 0..1 oscillating

        # Athan shine animation
        self._athan_shine_running = False
        self._athan_shine_cycle_start = None
        self._athan_shine_photo = None  # keep PhotoImage alive
        self._athan_overlay_base_image = None
        self._athan_overlay_photo = None
        self._athan_overlay_image_size = (0, 0)
        self._athan_overlay_image_path = None
        self._athan_overlay_time_text_id = None
        self._athan_overlay_iqamah_text_id = None
        self._athan_overlay_signature = None

        self.logo_base_image = None
        self.logo_image_path = None
        self.logo_image_mtime = None
        self.background_base_image = None
        self.background_photo_image = None
        self.background_image_size = (0, 0)
        self.background_image_path = None
        self._alpha_image_refs = {}
        self.prayer_box_fill_ids = {}
        self.prayer_box_fill_styles = {}
        
        # Iqamah countdown overlay (appears within 2 minutes of Iqamah)
        self.iqamah_overlay_visible = False
        self.iqamah_overlay_ids = []  # List of canvas IDs for overlay elements
        self.current_prayer_iqamah_time = None
        self.current_prayer_name = None
        self.iqamah_overlay_mode = None  # 'countdown', 'post', or 'khutbah'
        self.iqamah_post_duration_seconds = 180
        self.iqamah_overlay_cooldown_until = None
        self.iqamah_overlay_last_update = 0  # Timestamp to prevent rapid updates
        self._iqamah_countdown_text_transition_after_id = None
        self._iqamah_countdown_text_transition_temp_ids = []
        self._iqamah_countdown_text_transition_payload = None
        self._post_overlay_text_transition_after_id = None
        self._post_overlay_text_transition_temp_ids = []
        self._post_overlay_text_transition_payload = None
        self.iqamah_overlay_transition_duration_ms = 720
        self.iqamah_overlay_transition_tick_ms = 20
        self.post_overlay_transition_duration_ms = 860
        self.post_overlay_transition_tick_ms = 20
        self.post_overlay_transition_travel = self.us(12, 6)
        
        # Tracking for announcement ticker - initialize empty
        self.announcement_text_id = None
        self.announcement_text_ids = []  # List of all announcement text object IDs
        self.announcement_x_positions = []  # Starting x position of each item
        self.announcement_total_width = 0  # Total width of all announcements
        self.announcement_x_pos = 0  # Start off-screen to the right
        self.announcement_index = 0  # Track which announcement to show
        self.current_announcement = ""
        self.announcements = []
        self.ribbon_x = 0
        self.ribbon_y = 0
        self.ribbon_width = 0
        self.ribbon_height = 0
        
        # News tape hide/show cycle
        self.news_tape_hidden = False
        self.news_tape_hide_start = 0  # time.time() when hide began
        self.news_tape_hide_duration = 30  # seconds, loaded from config
        
        # Weather data
        self.show_weather = False
        self.weather_data = None  # {current_temp, current_icon, forecast: [{day, high, low, icon}, ...]}
        self.weather_lat = None
        self.weather_lon = None
        self.weather_last_fetch = 0
        self.weather_fetch_interval = 1800  # 30 minutes
        self._weather_fetching = False
        self._weather_show_forecast = False  # False=current temp, True=forecast
        self._weather_cycle_after_id = None
        self._weather_anim_after_id = None
        self._weather_anim_interval_ms = 95
        
        # Tracking for prayer time changes (tomorrow vs today)
        self.changing_prayers = {}  # {prayer_name: {today: time, tomorrow: time}}
        self._islamic_events_cache_date = None
        self._islamic_events_cache = []
        self.announcement_scroll_complete = False
        
        # Red ribbon visibility cycle (15 sec ON, 15 sec OFF)
        self.ribbon_cycle_counter = 0  # 0-29 seconds
        self.ribbon_visible = True  # Start visible
        self._ribbon_transition_running = False
        self._ribbon_transition_target_visible = True
        self._ribbon_transition_step = 0
        self._ribbon_transition_photo_refs = []
        self._ribbon_transition_ids = []
        
        # Tracking for upcoming prayer time changes (3+ days ahead)
        self.upcoming_changes = {}  # {prayer_name: {change_date: date, new_time: time, old_time: time}}
        self.upcoming_change_alerts = {}  # {prayer_name: display_info} for yellow ribbon
        self.dst_change_info = None  # {change_date, days_until, shift_minutes}
        
        # Tracking for yellow ribbon scrolling animation
        self.yellow_ribbon_text_ids = []  # List of text object IDs for yellow ribbon
        self.yellow_ribbon_x_positions = []  # Starting x position of each item
        self.yellow_ribbon_total_width = 0  # Total width of all changes text
        self.yellow_ribbon_x_pos = 0  # Current x position for scrolling
        self.yellow_ribbon_x = 0  # Yellow ribbon left position
        self.yellow_ribbon_y = 0  # Yellow ribbon top position
        self.yellow_ribbon_width = 0  # Yellow ribbon width
        self.yellow_ribbon_height = 0  # Yellow ribbon height
        self.yellow_ribbon_hidden = False  # Hide/show cycle state
        self.yellow_ribbon_hide_start = 0  # time.time() when hide began
        self.eid_ribbon_phase = 'english'  # english -> arabic -> english ...
        self.eid_ribbon_direction = -1  # -1: right-to-left, +1: left-to-right
        self.announcement_tick_ms = 100
        self.yellow_ribbon_tick_ms = 100
        self.salah_names_show_arabic = False
        self._last_salah_name_arabic_state = None
        self.salah_name_transition_active = False
        self.salah_name_transition_target_arabic = False
        self.salah_name_transition_after_id = None
        self.salah_name_transition_duration_ms = 280
        self.salah_name_transition_progress = 1.0
        self.salah_name_transition_tick_ms = 45
        self.salah_name_specs = []
        self.salah_name_canvas_ids = []
        
        # Jummah time (loaded from CSV or config/jummah.txt)
        self.jummah_time = None
        self.show_background_every_seconds = 60
        self.show_background_duration_seconds = 5
        self._background_cycle_started_mono = time.monotonic()
        self._background_cycle_visible = False

        # Test mode indicator canvas IDs (updated in-place)
        self.test_mode_box_id = None
        self.test_mode_label_id = None
        self.test_mode_info_id = None

        # Default show_logs to False (overridden by load_config if showlogs=yes)
        self.show_logs = False
        
        # Load prayer times AFTER initializing tracking
        try:
            self._log("[STARTUP] Loading configuration...", flush=True)
            self.load_config()
            self._log("[STARTUP] Loading prayer times...", flush=True)
            self.load_prayer_times()
            self._log("[STARTUP] Loading Jummah time...", flush=True)
            self.load_jummah_time()
            self._log("[STARTUP] Loading announcements...", flush=True)
            self.load_announcements()
            
            # Check for prayer changes early so toggle starts with data ready
            self._log("[STARTUP] Checking for upcoming prayer changes...", flush=True)
            self.check_upcoming_changes()  # Check for changes 3+ days ahead (must be first)
            self._log("[STARTUP] Checking for tomorrow's prayer changes...", flush=True)
            self.check_prayer_changes()  # Check for tomorrow's changes (depends on upcoming_changes)
            
            # Start the countdown update loop
            self._log("[STARTUP] Starting update schedulers...", flush=True)
            self.schedule_countdown_update()
            if not TEST_MODE:
                self.schedule_announcement_update()
                self.schedule_yellow_ribbon_update()  # Start yellow ribbon scrolling
                self.schedule_ribbon_cycle()  # Ribbon visibility cycle (15s ON, 45s OFF)
            if not TEST_MODE:
                self.schedule_csv_reload()  # Reload CSV every minute to catch updates
                self.root.after(3000, self.schedule_iqamah_countdown_check)  # Delay first overlay check to avoid startup flash
            if TEST_MODE:
                self.schedule_test_mode_update()  # Update test mode indicator time
            
            # Initial draw on startup
            self._log("[STARTUP] Drawing initial display...", flush=True)
            self.root.after(100, self.initial_draw)
            self.root.after(self.lantern_pulse_tick_ms, self.schedule_lantern_pulse_animation)
            self.root.after(self.star_twinkle_tick_ms, self.schedule_star_twinkle_animation)
            self.root.after(self.eid_animation_tick_ms, self.schedule_eid_animation)
            self.root.after(self.arafah_takbeer_tick_ms, self.schedule_arafah_takbeer_animation)
            self.root.after(self.takbeer_shower_tick_ms, self.schedule_takbeer_shower_animation)
            self.root.after(self.glow_tick_ms, self.schedule_glow_animation)
            if self.show_weather:
                self.root.after(500, self._start_weather_fetch)
            self.root.after(700, self._schedule_weather_animation)
        except Exception as e:
            self._log(f"[ERROR] Startup failed: {e}", flush=True)
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()
            import sys
            sys.exit(1)

    def _log(self, *args, **kwargs):
        """Print only when showlogs is enabled in settings."""
        if getattr(self, 'show_logs', False):
            print(*args, **kwargs)

    def set_ui_scale(self, width, height):
        """Update uniform UI scale based on current canvas size."""
        try:
            if width <= 1 or height <= 1:
                return
            width_scale = width / self.base_width
            height_scale = height / self.base_height
            self.ui_scale = max(0.65, min(1.6, min(width_scale, height_scale)))
        except:
            self.ui_scale = 1.0

    def us(self, value, minimum=1):
        """Scale a pixel value using current UI scale."""
        return max(minimum, int(round(value * self.ui_scale)))

    def fs(self, value, minimum=8):
        """Scale a font size using current UI scale."""
        return max(minimum, int(round(value * self.ui_scale)))

    def _startup_visibility_nudge(self):
        """Force window to front a few times during startup."""
        try:
            self.root.deiconify()
            self._enter_fullscreen()
            self.root.lift()
            self.root.attributes('-topmost', True)
            self.root.focus_force()
            self.root.after(120, lambda: self.root.attributes('-topmost', False))
        except:
            pass

        self._startup_nudge_attempts += 1
        if self._startup_nudge_attempts < 8:
            try:
                self.root.after(350, self._startup_visibility_nudge)
            except:
                pass

    def _on_window_mapped(self, event=None):
        """Apply fullscreen once the window is truly visible to avoid taskbar bleed-through."""
        if self._mapped_fullscreen_fix_done:
            return
        self._mapped_fullscreen_fix_done = True
        try:
            self.root.after(80, self._enter_fullscreen)
            self.root.after(380, self._enter_fullscreen)
        except:
            pass

    def _enter_fullscreen(self, event=None):
        """Enter reliable fullscreen, especially on Windows where taskbar can remain visible."""
        try:
            self.root.deiconify()
            screen_w = self.root.winfo_screenwidth()
            screen_h = self.root.winfo_screenheight()
            if sys.platform.startswith('win'):
                # Reset then reapply to force shell/taskbar recalculation.
                self.root.overrideredirect(False)
                self.root.state('normal')
                self.root.state('zoomed')
                self.root.update_idletasks()
                self.root.attributes('-fullscreen', True)
                self.root.overrideredirect(True)
                self.root.geometry(f"{screen_w}x{screen_h}+0+0")
                self.root.state('normal')
            self.root.attributes('-fullscreen', True)
            self.root.lift()
            self.root.attributes('-topmost', True)
            self.root.focus_force()
            self.root.after(120, lambda: self.root.attributes('-topmost', False))
        except:
            pass
        return 'break'

    def _exit_fullscreen(self, event=None):
        """Exit fullscreen and restore normal managed window state."""
        try:
            self.root.attributes('-fullscreen', False)
            if sys.platform.startswith('win'):
                self.root.overrideredirect(False)
            self.root.state('normal')
        except:
            pass
        return 'break'

    def _toggle_fullscreen(self, event=None):
        """Toggle fullscreen mode with Windows-safe behavior."""
        try:
            is_fullscreen = bool(self.root.attributes('-fullscreen'))
        except:
            is_fullscreen = False
        if is_fullscreen:
            return self._exit_fullscreen(event)
        return self._enter_fullscreen(event)
        
    def get_current_date(self):
        """Get current date, respecting test mode"""
        if TEST_MODE and TEST_DATE:
            try:
                mocked_date = datetime.strptime(TEST_DATE, "%Y-%m-%d").date()
                if not self._test_mode_date_logged:
                    self._log(f"[DATE] TEST MODE: Using mocked date {mocked_date} (System date: {datetime.now().date()})")
                    self._test_mode_date_logged = True
                return mocked_date
            except:
                if not self._test_mode_date_error_logged:
                    self._log(f"Invalid TEST_DATE format: {TEST_DATE}. Using system date.")
                    self._test_mode_date_error_logged = True
                return datetime.now().date()
        return datetime.now().date()
    
    def get_current_time(self):
        """Get current time, respecting test mode"""
        if TEST_MODE and TEST_TIME:
            try:
                # Parse the initial TEST_TIME
                base_time = datetime.strptime(TEST_TIME, "%H:%M:%S")
                
                # If we have a start time, calculate elapsed seconds and add to base time
                if self.test_mode_start_time:
                    elapsed = (datetime.now() - self.test_mode_start_time).total_seconds()
                    # Add elapsed seconds to base time
                    current_datetime = base_time + timedelta(seconds=elapsed)
                    return current_datetime.time()
                else:
                    return base_time.time()
            except:
                if not self._test_mode_time_error_logged:
                    self._log(f"Invalid TEST_TIME format: {TEST_TIME}. Using system time.")
                    self._test_mode_time_error_logged = True
                return datetime.now().time()
        return datetime.now().time()

    def should_show_periodic_background_image(self):
        """Return True only during the configured periodic background-image window."""
        if getattr(self, 'iqamah_overlay_visible', False):
            return False

        every = max(0, int(getattr(self, 'show_background_every_seconds', 0) or 0))
        duration = max(0, int(getattr(self, 'show_background_duration_seconds', 0) or 0))

        if every <= 0 or duration <= 0:
            return False

        cycle_length = every + duration
        if cycle_length <= 0:
            return False

        elapsed = max(0.0, time.monotonic() - getattr(self, '_background_cycle_started_mono', time.monotonic()))
        phase = elapsed % cycle_length
        return phase >= every

    def handle_date_rollover(self, new_date):
        """Refresh data and full UI when calendar date changes."""
        if self._date_rollover_refresh_in_progress:
            return

        self._date_rollover_refresh_in_progress = True
        try:
            self._last_seen_date = new_date
            self._log(f"[DATE] Day changed to {new_date}; refreshing display/data...")

            if self.iqamah_overlay_visible:
                self.hide_iqamah_overlay()

            self.load_prayer_times()
            self.load_announcements()
            self.check_upcoming_changes()
            self.check_prayer_changes()
            self.redraw_full_display()
        except Exception as e:
            self._log(f"ERROR in handle_date_rollover: {e}")
        finally:
            self._date_rollover_refresh_in_progress = False
    
    def initial_draw(self):
        """Initial draw of the display"""
        try:
            width = self.canvas.winfo_width()
            height = self.canvas.winfo_height()
            
            # If canvas not ready yet, retry in 50ms
            if width <= 1 or height <= 1:
                self.root.after(50, self.initial_draw)
                return
                
            # Draw prayer times first (fast) - skip heavy background rendering
            self.draw_prayer_times()
            self.draw_test_mode_indicator()  # Show test mode info if enabled
            self._log("[STARTUP] [OK] App startup complete - rendering background...")
            
            # Defer Islamic background generation to after window is visible
            self.root.after(100, self._generate_and_apply_background_deferred)
        except Exception as e:
            self._log(f"ERROR in initial_draw: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()
    
    def _generate_and_apply_background_deferred(self):
        """Generate and apply Islamic background after window is visible"""
        try:
            athan_running = bool(getattr(self, '_athan_shine_running', False) and self.athan_callout_prayer)
            # Redraw in proper z-order: background first, then foreground content
            self.canvas.delete('all')
            self.draw_islamic_background()
            self.draw_prayer_times()
            self.draw_test_mode_indicator()
            if athan_running:
                self._draw_athan_shine_frame(0)

            # Keep overlays above foreground content
            self.canvas.tag_raise('iqamah_overlay')
            
            self._log("[STARTUP] Background rendering complete!")
        except Exception as e:
            self._log(f"ERROR in _generate_and_apply_background_deferred: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()
        
    def on_resize(self, event):
        """Redraw when window is resized"""
        # Skip redraw if overlay is active to keep it stable
        if self.iqamah_overlay_visible:
            return
        
        # Only redraw if canvas has valid dimensions
        if event.width > 1 and event.height > 1:
            # Debounce rapid resize events to avoid redraw storms/freezes
            if self._resize_redraw_job:
                try:
                    self.root.after_cancel(self._resize_redraw_job)
                except:
                    pass

            self._resize_redraw_job = self.root.after(120, self._perform_resize_redraw)

    def _perform_resize_redraw(self):
        """Perform a single redraw after resize debounce"""
        self._resize_redraw_job = None
        try:
            if self.iqamah_overlay_visible:
                return
            self.redraw_full_display()
        except Exception as e:
            self._log(f"ERROR in _perform_resize_redraw: {e}")

    def redraw_full_display(self):
        """Redraw full canvas in correct z-order."""
        if self._is_full_redraw:
            return

        self._is_full_redraw = True
        try:
            # Remember overlay state before wiping canvas
            overlay_was_visible = self.iqamah_overlay_visible
            overlay_mode = self.iqamah_overlay_mode
            athan_running = bool(getattr(self, '_athan_shine_running', False) and self.athan_callout_prayer)
            self.canvas.delete('all')
            self._alpha_image_refs = {}
            self.prayer_box_fill_ids = {}
            self.prayer_box_fill_styles = {}
            if self._weather_cycle_after_id:
                try:
                    self.root.after_cancel(self._weather_cycle_after_id)
                except:
                    pass
                self._weather_cycle_after_id = None
            if self.should_show_periodic_background_image():
                width = self.canvas.winfo_width()
                height = self.canvas.winfo_height()
                if not self.draw_background_image(width, height):
                    self.draw_islamic_background()
                self.draw_background_image_label(width, height)
            else:
                self.draw_islamic_background()
                self.draw_prayer_times()
                self.draw_test_mode_indicator()
            if athan_running:
                self._draw_athan_shine_frame(0)
            # Re-show iqamah overlay if it was active (canvas.delete wiped it)
            if overlay_was_visible:
                self.iqamah_overlay_ids = []
                if overlay_mode == 'post':
                    self.show_post_iqamah_overlay()
                elif overlay_mode == 'khutbah':
                    self.show_khutbah_overlay()
                else:
                    self.show_iqamah_overlay()
        finally:
            self._is_full_redraw = False

    def schedule_lantern_pulse_animation(self):
        """Refresh Ramadan lanterns so they continuously dim/brighten."""
        try:
            if self.is_ramadan(self.get_current_date()) and not self.iqamah_overlay_visible and not self._is_full_redraw:
                self.update_lanterns_only()
        except Exception as e:
            self._log(f"ERROR in schedule_lantern_pulse_animation: {e}")
        finally:
            try:
                self.root.after(self.lantern_pulse_tick_ms, self.schedule_lantern_pulse_animation)
            except:
                pass

    def schedule_star_twinkle_animation(self):
        """Refresh Ramadan stars so they continuously twinkle."""
        try:
            if self.is_ramadan(self.get_current_date()) and not self.iqamah_overlay_visible and not self._is_full_redraw:
                self.update_stars_only()
        except Exception as e:
            self._log(f"ERROR in schedule_star_twinkle_animation: {e}")
        finally:
            try:
                self.root.after(self.star_twinkle_tick_ms, self.schedule_star_twinkle_animation)
            except:
                pass

    def schedule_eid_animation(self):
        """Refresh galaxy stars so they continuously glow/dim/lighten."""
        try:
            if (not self.is_ramadan(self.get_current_date())) and not self.iqamah_overlay_visible and not self._is_full_redraw:
                self.update_eid_effects_only()
        except Exception as e:
            self._log(f"ERROR in schedule_eid_animation: {e}")
        finally:
            try:
                self.root.after(self.eid_animation_tick_ms, self.schedule_eid_animation)
            except:
                pass

    def schedule_glow_animation(self):
        """Pulse a glow on the current prayer box border every few seconds."""
        try:
            if not self.iqamah_overlay_visible and not self._is_full_redraw:
                theme_name = self.get_theme_name()
                no_outline_mode = (theme_name == 'elegent_v2')
                # Advance phase 0..1 for a full pulse cycle.
                step = self.glow_tick_ms / 1000.0 / self.glow_cycle_seconds
                self._glow_phase = (self._glow_phase + step) % 1.0

                # Short pulse window inside each cycle.
                pulse_window = 0.22
                pulse = 0.0
                if self._glow_phase < pulse_window:
                    t = self._glow_phase / pulse_window
                    pulse = math.sin(t * math.pi)

                # Update only the current prayer box with a soft glow pulse.
                # Skip entirely while any athan warning is active.
                current = self.last_rendered_current_prayer
                if current and current in self.prayer_box_fill_ids and self.athan_callout_prayer is None and theme_name != 'elegent_v2':
                    palette = self.get_theme_palette()
                    outline_width = 0 if no_outline_mode else (self.us(4, 2) + int(round(self.us(2, 1) * pulse)))
                    outline_alpha = 150 + int(round(90 * pulse))
                    glow_outline = self._mix_hex_color(
                        palette['card_current_outline'],
                        '#fff1a8',
                        0.65 * pulse
                    )
                    if no_outline_mode:
                        glow_outline = ''
                    glow_fill = self._mix_hex_color(
                        palette['card_current_fill'],
                        '#fff8d9',
                        0.18 * pulse
                    )
                    self.update_prayer_box_alpha_fill(
                        current,
                        glow_fill,
                        glow_outline,
                        outline_width,
                        outline_alpha=outline_alpha,
                        animated_line=False
                    )
        except Exception as e:
            self._log(f"ERROR in schedule_glow_animation: {e}")
        finally:
            try:
                self.root.after(self.glow_tick_ms, self.schedule_glow_animation)
            except:
                pass

    def update_eid_effects_only(self):
        """Update animated galaxy stars, plus Eid overlays on Eid day only."""
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        if width <= 1 or height <= 1:
            return

        self.canvas.delete('animated_galaxy_stars')
        self.draw_eid_star_fields(width, height, animated=True, tags='animated_galaxy_stars')
        self.canvas.tag_raise('animated_galaxy_stars')

        if self.is_eid_day(self.get_current_date()):
            self.canvas.delete('animated_eid')
            self.draw_eid_fireworks(width, height, animated=True, tags='animated_eid')
            self.draw_eid_balloons(width, height, animated=True, tags='animated_eid')
            self.canvas.tag_raise('animated_eid')
        else:
            self.canvas.delete('animated_eid')

    def schedule_arafah_takbeer_animation(self):
        """Advance the Arafah Takbeer prayer-box cycle within the configured date range."""
        try:
            if self.get_theme_name() != 'elegent_v2':
                return
            if self.iqamah_overlay_visible or self._is_full_redraw:
                return
            if self._advance_arafah_takbeer_cycle():
                self.redraw_full_display()
        except Exception as e:
            self._log(f"ERROR in schedule_arafah_takbeer_animation: {e}")
        finally:
            try:
                self.root.after(self.arafah_takbeer_tick_ms, self.schedule_arafah_takbeer_animation)
            except:
                pass

    def _should_draw_takbeer_shower(self):
        if self.get_theme_name() != 'elegent_v2':
            return False
        if not bool(getattr(self, 'show_arafah_takbeer_panel', True)):
            return False
        if not bool(getattr(self, 'show_takbeer_shower', True)):
            return False
        if bool(getattr(self, 'athan_callout_prayer', None)):
            return False
        if self.iqamah_overlay_visible:
            return False
        if not self.is_takbeer_shower_window(self.get_current_date()):
            return False
        return True

    def schedule_takbeer_shower_animation(self):
        """Animate takbeer lines showering downward using the same show/pause interval cycle."""
        try:
            if self._is_full_redraw:
                return

            if not self._should_draw_takbeer_shower():
                self.canvas.delete('takbeer_shower')
                self.arafah_takbeer_particles = []
                self.takbeer_shower_last_tick_mono = None
                return

            width = max(1, self.canvas.winfo_width())
            height = max(1, self.canvas.winfo_height())

            now_mono = time.monotonic()
            if self.takbeer_shower_last_tick_mono is None:
                dt = max(0.01, self.takbeer_shower_tick_ms / 1000.0)
            else:
                dt = max(0.01, min(0.12, now_mono - self.takbeer_shower_last_tick_mono))
            self.takbeer_shower_last_tick_mono = now_mono

            lanes = [0.24, 0.5, 0.76]
            spawn_y = -float(self.us(70, 36))
            despawn_y = float(height + self.us(120, 70))
            fall_speed = float(self.us(170, 100))
            particle_font_size = self.fs(40, 22)

            existing_by_lane = {}
            for particle in list(getattr(self, 'arafah_takbeer_particles', [])):
                try:
                    lane_idx = int(particle.get('lane', -1))
                except Exception:
                    lane_idx = -1
                if lane_idx < 0 or lane_idx >= len(lanes):
                    item_id = particle.get('id')
                    outline_ids = list(particle.get('outline_ids', []))
                    if item_id:
                        try:
                            self.canvas.delete(item_id)
                        except:
                            pass
                    for outline_id in outline_ids:
                        try:
                            self.canvas.delete(outline_id)
                        except:
                            pass
                    continue
                if lane_idx not in existing_by_lane:
                    existing_by_lane[lane_idx] = particle
                else:
                    item_id = particle.get('id')
                    outline_ids = list(particle.get('outline_ids', []))
                    if item_id:
                        try:
                            self.canvas.delete(item_id)
                        except:
                            pass
                    for outline_id in outline_ids:
                        try:
                            self.canvas.delete(outline_id)
                        except:
                            pass

            shower_text = str(getattr(self, 'arafah_takbeer_shower_text', '') or '').strip()
            if not shower_text:
                shower_text = '\n\n'.join(self.arafah_takbeer_lines[:3])

            next_particles = []
            for lane_idx in range(len(lanes)):
                lane_x = int(width * lanes[lane_idx])
                particle = existing_by_lane.get(lane_idx, {
                    'id': None,
                    'lane': lane_idx,
                    'text': shower_text,
                    'y': float(spawn_y),
                    'vy': float(fall_speed),
                })
                particle['text'] = shower_text

                item_id = particle.get('id')
                outline_ids = list(particle.get('outline_ids', []))
                item_alive = False
                if item_id:
                    try:
                        item_alive = bool(self.canvas.type(item_id))
                    except:
                        item_alive = False
                outline_alive = False
                if outline_ids:
                    try:
                        outline_alive = all(bool(self.canvas.type(oid)) for oid in outline_ids)
                    except:
                        outline_alive = False

                if (not item_alive) or (not outline_alive):
                    if item_id:
                        try:
                            self.canvas.delete(item_id)
                        except:
                            pass
                    for outline_id in outline_ids:
                        try:
                            self.canvas.delete(outline_id)
                        except:
                            pass

                    outline_offsets = [(-2, -2), (-2, 0), (-2, 2), (0, -2), (0, 2), (2, -2), (2, 0), (2, 2)]
                    outline_ids = []
                    outline_specs = []
                    for dx, dy in outline_offsets:
                        oid = self.canvas.create_text(
                            lane_x + dx,
                            spawn_y + dy,
                            text=shower_text,
                            font=('Traditional Arabic', particle_font_size, 'bold'),
                            fill='#000000',
                            anchor='n',
                            justify='center',
                            tags=('takbeer_shower',)
                        )
                        outline_ids.append(oid)
                        outline_specs.append((oid, dx, dy))
                    item_id = self.canvas.create_text(
                        lane_x,
                        spawn_y,
                        text=shower_text,
                        font=('Traditional Arabic', particle_font_size, 'bold'),
                        fill='#f8fbff',
                        anchor='n',
                        justify='center',
                        tags=('takbeer_shower',)
                    )
                    particle['id'] = item_id
                    particle['outline_ids'] = outline_ids
                    particle['outline_specs'] = outline_specs
                    particle['y'] = float(spawn_y)

                y_new = float(particle.get('y', spawn_y)) + (float(particle.get('vy', fall_speed)) * dt)
                if y_new > despawn_y:
                    y_new = float(spawn_y)
                particle['y'] = y_new
                try:
                    outline_specs = list(particle.get('outline_specs', []))
                    if outline_specs:
                        for outline_id, dx, dy in outline_specs:
                            self.canvas.coords(outline_id, lane_x + dx, y_new + dy)
                            self.canvas.itemconfig(outline_id, text=shower_text)
                    else:
                        for outline_id in list(particle.get('outline_ids', [])):
                            self.canvas.coords(outline_id, lane_x - 2, y_new - 2)
                            self.canvas.itemconfig(outline_id, text=shower_text)
                    self.canvas.coords(item_id, lane_x, y_new)
                    self.canvas.itemconfig(item_id, text=shower_text)
                except:
                    pass
                next_particles.append(particle)

            self.arafah_takbeer_particles = next_particles

            self.canvas.tag_raise('takbeer_shower')
        except Exception as e:
            self._log(f"ERROR in schedule_takbeer_shower_animation: {e}")
        finally:
            try:
                self.root.after(self.takbeer_shower_tick_ms, self.schedule_takbeer_shower_animation)
            except:
                pass

    def _parse_config_date(self, value):
        """Parse a date string from settings into a date object."""
        text = str(value or '').strip()
        if not text:
            return None
        for fmt in ('%Y-%m-%d', '%Y/%m/%d', '%m/%d/%Y', '%d/%m/%Y', '%b %d %Y', '%B %d %Y'):
            try:
                return datetime.strptime(text, fmt).date()
            except:
                continue
        return None

    def is_arafah_takbeer_window(self, date_obj):
        """True when current date is within configured Arafah Takbeer date range."""
        start = getattr(self, 'arafah_takbeer_start_date', None)
        end = getattr(self, 'arafah_takbeer_end_date', None)
        if not start or not end:
            return False
        if end < start:
            return False
        if not (start <= date_obj <= end):
            return False

        # On the configured end date, stop at today's Maghrib Athan time.
        if date_obj == end and date_obj == self.get_current_date():
            try:
                prayers_data = self.get_today_prayers() or {}
                maghrib_athan = self.parse_time(prayers_data.get('MaghribAthan', ''))
                if maghrib_athan:
                    return self.get_current_time() < maghrib_athan
            except:
                pass

        return True

    def is_takbeer_shower_window(self, date_obj):
        """True for the four days after configured start date (e.g. 27-30 when start is 26)."""
        start = getattr(self, 'arafah_takbeer_start_date', None)
        if not start:
            return False
        shower_start = start + timedelta(days=1)
        shower_end = start + timedelta(days=4)
        return shower_start <= date_obj <= shower_end

    def _is_takbeer_cycle_window(self, date_obj):
        return self.is_arafah_takbeer_window(date_obj) or self.is_takbeer_shower_window(date_obj)

    def _reset_arafah_takbeer_cycle(self):
        self.arafah_takbeer_cycle_phase = 'show'
        self.arafah_takbeer_cycle_index = 0
        self.arafah_takbeer_cycle_started_mono = time.monotonic()

    def _get_arafah_takbeer_active_key(self):
        if not self._is_takbeer_cycle_window(self.get_current_date()):
            return None
        if self.arafah_takbeer_cycle_phase != 'show':
            return None
        if not self.arafah_takbeer_cycle_order:
            return None
        index = max(0, min(self.arafah_takbeer_cycle_index, len(self.arafah_takbeer_cycle_order) - 1))
        return self.arafah_takbeer_cycle_order[index]

    def _advance_arafah_takbeer_cycle(self):
        if self.get_theme_name() != 'elegent_v2':
            if self.arafah_takbeer_cycle_phase != 'off' or self.arafah_takbeer_cycle_index != 0:
                self.arafah_takbeer_cycle_phase = 'off'
                self.arafah_takbeer_cycle_index = 0
                self.arafah_takbeer_cycle_started_mono = time.monotonic()
                return True
            return False

        if not self._is_takbeer_cycle_window(self.get_current_date()):
            if self.arafah_takbeer_cycle_phase != 'off' or self.arafah_takbeer_cycle_index != 0:
                self.arafah_takbeer_cycle_phase = 'off'
                self.arafah_takbeer_cycle_index = 0
                self.arafah_takbeer_cycle_started_mono = time.monotonic()
                return True
            return False

        now_mono = time.monotonic()
        elapsed = now_mono - float(getattr(self, 'arafah_takbeer_cycle_started_mono', now_mono))
        changed = False

        if self.arafah_takbeer_cycle_phase == 'off':
            self.arafah_takbeer_cycle_phase = 'show'
            self.arafah_takbeer_cycle_index = 0
            self.arafah_takbeer_cycle_started_mono = now_mono
            return True

        is_shower_day = self.is_takbeer_shower_window(self.get_current_date())
        display_seconds = float(self.arafah_takbeer_display_seconds)
        if is_shower_day:
            # Shower mode stays on longer so falling lines can reach the bottom.
            display_seconds = max(1.0, display_seconds * 2.0)

        if is_shower_day:
            # In shower mode, keep a full off phase after the longer show window.
            hidden_seconds = max(1.0, float(self.arafah_takbeer_pause_seconds))
        else:
            hidden_seconds = max(1.0, float(self.arafah_takbeer_pause_seconds) - float(self.arafah_takbeer_display_seconds))

        if self.arafah_takbeer_cycle_phase == 'show':
            if elapsed >= display_seconds:
                self.arafah_takbeer_cycle_phase = 'pause'
                self.arafah_takbeer_cycle_started_mono = now_mono
                changed = True
        elif self.arafah_takbeer_cycle_phase == 'pause':
            if elapsed >= hidden_seconds:
                self.arafah_takbeer_cycle_phase = 'show'
                if self.arafah_takbeer_cycle_order:
                    self.arafah_takbeer_cycle_index = (self.arafah_takbeer_cycle_index + 1) % len(self.arafah_takbeer_cycle_order)
                else:
                    self.arafah_takbeer_cycle_index = 0
                self.arafah_takbeer_cycle_started_mono = now_mono
                changed = True

        return changed

    def draw_arafah_takbeer_rain(self, width, height, animated=True, tags='animated_takbeer_rain'):
        """Deprecated placeholder retained for compatibility; takbeer rain was removed."""
        return

    def update_lanterns_only(self):
        """Update only the lantern visuals without redrawing the entire display."""
        return  # Lanterns disabled

    def update_stars_only(self):
        """Update only star visuals with twinkling effect without redrawing entire display."""
        return  # Stars disabled
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        if width <= 1 or height <= 1:
            return

        self.canvas.delete('animated_stars')
        bottom_star_cutoff = 0.82

        base_size = min(width, height) * 0.008
        star_points = [
            (0.08, 0.20, 1.0), (0.18, 0.28, 0.7), (0.30, 0.22, 0.9), (0.43, 0.26, 0.8),
            (0.57, 0.21, 0.6), (0.69, 0.29, 0.9), (0.82, 0.23, 1.0), (0.90, 0.31, 0.7),
            (0.10, 0.44, 1.1), (0.24, 0.47, 0.8), (0.38, 0.43, 1.0), (0.52, 0.46, 0.7),
            (0.66, 0.42, 1.0), (0.80, 0.48, 0.9), (0.13, 0.62, 1.2), (0.27, 0.67, 0.8),
            (0.41, 0.61, 1.0), (0.56, 0.66, 0.7), (0.72, 0.62, 1.1), (0.86, 0.68, 0.9),
            (0.18, 0.80, 1.0), (0.34, 0.84, 0.8), (0.52, 0.81, 1.0), (0.70, 0.86, 0.9),
            (0.84, 0.82, 1.1),
            (0.05, 0.13, 0.55), (0.14, 0.17, 1.25), (0.22, 0.14, 0.65), (0.33, 0.16, 1.35),
            (0.47, 0.15, 0.60), (0.61, 0.17, 1.30), (0.74, 0.14, 0.70), (0.88, 0.16, 1.20),
            (0.06, 0.35, 0.75), (0.17, 0.38, 1.40), (0.29, 0.36, 0.65), (0.46, 0.39, 1.25),
            (0.59, 0.34, 0.70), (0.73, 0.37, 1.30), (0.91, 0.40, 0.60),
            (0.09, 0.54, 0.65), (0.20, 0.57, 1.35), (0.35, 0.53, 0.75), (0.49, 0.56, 1.20),
            (0.63, 0.58, 0.65), (0.77, 0.55, 1.40), (0.90, 0.59, 0.70),
            (0.07, 0.73, 0.60), (0.23, 0.74, 1.30), (0.31, 0.77, 0.70), (0.46, 0.75, 1.45),
            (0.60, 0.79, 0.60), (0.75, 0.76, 1.25), (0.92, 0.72, 0.65),
            (0.12, 0.90, 1.30), (0.28, 0.92, 0.65), (0.44, 0.90, 1.20), (0.62, 0.93, 0.70),
            (0.78, 0.91, 1.35), (0.94, 0.89, 0.60)
        ]

        for sx, sy, scale in star_points:
            if sy >= bottom_star_cutoff:
                continue
            twinkle_phase = ((time.time() / self.star_twinkle_cycle_seconds) * (2 * math.pi)) + (sx * sy * 10)
            twinkle_t = 0.5 + (0.5 * math.sin(twinkle_phase))
            brightness = 0.4 + (0.6 * twinkle_t)
            color = self._mix_hex_color('#9f8a3b', '#f2d675', brightness)
            self.draw_small_star(width * sx, height * sy, base_size * scale, color, tags='animated_stars')

    def _mix_hex_color(self, color_a, color_b, t):
        """Blend two #RRGGBB colors by factor t in [0, 1]."""
        t = max(0.0, min(1.0, float(t)))
        a = color_a.lstrip('#')
        b = color_b.lstrip('#')
        ar, ag, ab = int(a[0:2], 16), int(a[2:4], 16), int(a[4:6], 16)
        br, bg, bb = int(b[0:2], 16), int(b[2:4], 16), int(b[4:6], 16)
        r = int(round(ar + (br - ar) * t))
        g = int(round(ag + (bg - ag) * t))
        bl = int(round(ab + (bb - ab) * t))
        return f'#{r:02x}{g:02x}{bl:02x}'

    def schedule_transition_redraw(self, expected_current_prayer):
        """Queue a single transition redraw to avoid blocking timer loops."""
        if self._transition_redraw_pending:
            return

        self._transition_redraw_pending = True

        def _do_redraw():
            try:
                self.redraw_full_display()
                self.last_rendered_current_prayer = expected_current_prayer
                self._last_transition_redraw_at = datetime.now().timestamp()
            finally:
                self._transition_redraw_pending = False

        try:
            self.root.after_idle(_do_redraw)
        except:
            self._transition_redraw_pending = False

    def draw_test_mode_indicator(self):
        """Display test mode indicator with current test date/time at top of screen"""
        if not TEST_MODE:
            return
        
        width = self.canvas.winfo_width()
        current_date = self.get_current_date()
        current_time = datetime.now().strftime('%I:%M:%S %p')
        
        # Create semi-transparent background box
        box_height = 50
        self.test_mode_box_id = self.canvas.create_rectangle(
            0, 0, width, box_height,
            fill='#ff6b6b',  # Red background
            outline='#cc0000',
            width=3,
            tags='test_mode_indicator'
        )
        
        # Display TEST MODE text on left
        self.test_mode_label_id = self.canvas.create_text(
            20, box_height/2,
            text="TEST MODE",
            font=('Arial', 18, 'bold'),
            fill='white',
            anchor='w',
            tags='test_mode_indicator'
        )
        
        # Display test date and time on right
        test_info = f"Test Date: {current_date}  |  Time: {current_time}"
        self.test_mode_info_id = self.canvas.create_text(
            width - 20, box_height/2,
            text=test_info,
            font=('Arial', 16, 'bold'),
            fill='white',
            anchor='e',
            tags='test_mode_indicator'
        )
    
    def draw_islamic_background(self):
        """Draw Islamic geometric patterns"""
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        
        if width <= 1 or height <= 1:
            return

        if self.draw_background_image(width, height):
            self.draw_background_image_label(width, height)
            return

        theme = self.get_theme_name()
        current_date = self.get_current_date()

        if theme == 'ramadan':
            self.draw_ramadan_background(width, height)
            return

        if theme == 'modern':
            self.draw_modern_background(width, height)
            return

        if theme == 'elegent':
            self.draw_elegent_background(width, height)
            return

        if theme == 'elegent_v2':
            self.draw_elegent_background(width, height)
            return

        if self.is_ramadan(current_date):
            self.draw_ramadan_background(width, height)
            return

        # Default background now uses the Milky Way style (without Eid overlays).
        self.draw_eid_background(width, height)

    def draw_modern_background(self, width, height):
        """Draw modern blue-slate gradient background with subtle accent glows."""
        gradient_steps = 60
        top_r, top_g, top_b = (15, 23, 42)   # #0f172a
        bot_r, bot_g, bot_b = (30, 41, 59)   # #1e293b

        for i in range(gradient_steps):
            ratio = i / max(1, gradient_steps - 1)
            r = int(top_r + (bot_r - top_r) * ratio)
            g = int(top_g + (bot_g - top_g) * ratio)
            b = int(top_b + (bot_b - top_b) * ratio)
            color = f'#{r:02x}{g:02x}{b:02x}'
            y_pos = (height * i) / gradient_steps
            self.canvas.create_rectangle(
                0, y_pos, width, y_pos + (height / gradient_steps) + 2,
                fill=color,
                outline=''
            )

        self.draw_eid_star_fields(width, height, animated=False, tags=None)

    def draw_elegent_background(self, width, height):
        """Draw an elegant minimal background focused on the mosque silhouette."""
        gradient_steps = 64
        top_r, top_g, top_b = (6, 12, 28)
        mid_r, mid_g, mid_b = (21, 35, 64)
        bot_r, bot_g, bot_b = (12, 20, 40)

        for i in range(gradient_steps):
            ratio = i / max(1, gradient_steps - 1)
            if ratio < 0.55:
                local = ratio / 0.55
                r = int(top_r + (mid_r - top_r) * local)
                g = int(top_g + (mid_g - top_g) * local)
                b = int(top_b + (mid_b - top_b) * local)
            else:
                local = (ratio - 0.55) / 0.45
                r = int(mid_r + (bot_r - mid_r) * local)
                g = int(mid_g + (bot_g - mid_g) * local)
                b = int(mid_b + (bot_b - mid_b) * local)

            color = f'#{r:02x}{g:02x}{b:02x}'
            y_pos = (height * i) / gradient_steps
            self.canvas.create_rectangle(
                0, y_pos, width, y_pos + (height / gradient_steps) + 2,
                fill=color,
                outline=''
            )

        self.draw_elegent_mosque_silhouette(width, height)

    def draw_elegent_mosque_silhouette(self, width, height):
        """Draw a large mosque silhouette for the elegent theme."""
        base_color = '#0a1429'
        accent_color = '#14233f'
        cutout_color = '#1a2b4f'

        horizon_y = height * 0.80
        self.canvas.create_rectangle(0, horizon_y, width, height, fill=base_color, outline='')

        center_x = width / 2
        body_w = width * 0.58
        body_h = height * 0.20
        body_top = horizon_y - body_h

        self.canvas.create_rectangle(
            center_x - (body_w / 2),
            body_top,
            center_x + (body_w / 2),
            horizon_y,
            fill=accent_color,
            outline=''
        )

        dome_r = min(width, height) * 0.13
        dome_cy = body_top
        self.canvas.create_oval(
            center_x - dome_r,
            dome_cy - dome_r,
            center_x + dome_r,
            dome_cy + dome_r,
            fill=accent_color,
            outline=''
        )

        # Side domes for a grand silhouette.
        side_r = dome_r * 0.55
        for sx in (center_x - body_w * 0.24, center_x + body_w * 0.24):
            self.canvas.create_oval(
                sx - side_r,
                body_top - side_r,
                sx + side_r,
                body_top + side_r,
                fill=accent_color,
                outline=''
            )

        # Main entrance arch cutout.
        gate_w = body_w * 0.18
        gate_h = body_h * 0.62
        gate_x1 = center_x - (gate_w / 2)
        gate_x2 = center_x + (gate_w / 2)
        gate_y2 = horizon_y
        gate_y1 = gate_y2 - gate_h
        self.canvas.create_rectangle(gate_x1, gate_y1, gate_x2, gate_y2, fill=cutout_color, outline='')
        self.canvas.create_oval(gate_x1, gate_y1 - (gate_w * 0.35), gate_x2, gate_y1 + (gate_w * 0.35), fill=cutout_color, outline='')

        # Repeating smaller arch cutouts.
        small_arch_w = body_w * 0.09
        small_arch_h = body_h * 0.42
        for i in range(-3, 4):
            if i == 0:
                continue
            arch_cx = center_x + i * body_w * 0.095
            ax1 = arch_cx - (small_arch_w / 2)
            ax2 = arch_cx + (small_arch_w / 2)
            ay2 = horizon_y
            ay1 = ay2 - small_arch_h
            self.canvas.create_rectangle(ax1, ay1, ax2, ay2, fill=cutout_color, outline='')
            self.canvas.create_oval(ax1, ay1 - (small_arch_w * 0.30), ax2, ay1 + (small_arch_w * 0.30), fill=cutout_color, outline='')

        # Twin minarets.
        minaret_h = height * 0.36
        minaret_w = body_w * 0.065
        for mx in (center_x - body_w * 0.40, center_x + body_w * 0.40):
            top_y = horizon_y - minaret_h
            self.canvas.create_rectangle(
                mx - (minaret_w / 2),
                top_y,
                mx + (minaret_w / 2),
                horizon_y,
                fill=accent_color,
                outline=''
            )
            balcony_h = minaret_h * 0.08
            self.canvas.create_rectangle(
                mx - (minaret_w * 0.70),
                top_y + (minaret_h * 0.38),
                mx + (minaret_w * 0.70),
                top_y + (minaret_h * 0.38) + balcony_h,
                fill=accent_color,
                outline=''
            )
            self.canvas.create_polygon(
                mx,
                top_y - (minaret_w * 0.9),
                mx - (minaret_w * 0.45),
                top_y,
                mx + (minaret_w * 0.45),
                top_y,
                fill=accent_color,
                outline=''
            )

    def draw_ramadan_background(self, width, height):
        """Draw Ramadan-only purple background with gold hanging motifs (sample style)."""
        gradient_steps = 56
        top_r, top_g, top_b = (34, 11, 92)
        bot_r, bot_g, bot_b = (47, 17, 112)

        for i in range(gradient_steps):
            ratio = i / max(1, gradient_steps - 1)
            r = int(top_r + (bot_r - top_r) * ratio)
            g = int(top_g + (bot_g - top_g) * ratio)
            b = int(top_b + (bot_b - top_b) * ratio)
            color = f'#{r:02x}{g:02x}{b:02x}'
            y_pos = (height * i) / gradient_steps
            self.canvas.create_rectangle(
                0, y_pos, width, y_pos + (height / gradient_steps) + 2,
                fill=color,
                outline=''
            )

        self.draw_ramadan_hanging_motifs(width, height)
        self.draw_ramadan_stars(width, height)

    def draw_ramadan_hanging_motifs(self, width, height):
        """Draw top hanging strings with crescent/star/lantern motifs."""
        unit = min(width, height)
        top_y = height * 0.03
        line_color = '#d4af37'
        line_bottom = top_y + (unit * 0.12)

        # (x_ratio, kind, size_ratio)
        motifs = [
            (0.10, 'crescent', 0.048),
            (0.24, 'crescent', 0.040),
            (0.36, 'star', 0.030),
            (0.50, 'crescent', 0.048),
            (0.64, 'star', 0.030),
            (0.76, 'crescent', 0.040),
            (0.90, 'crescent', 0.048),
        ]

        for x_ratio, kind, size_ratio in motifs:
            x = width * x_ratio
            size = unit * size_ratio
            end_x = x
            end_y = line_bottom
            self.canvas.create_line(
                x,
                top_y,
                end_x,
                end_y,
                fill=line_color,
                width=max(1, int(unit * 0.002))
            )

            if kind == 'crescent':
                self._draw_ramadan_single_crescent(end_x, end_y + size * 0.42, size)
            elif kind == 'star':
                self.draw_small_star(end_x, end_y + size * 0.85, size * 0.95, '#f2d675')
            else:
                self.draw_ramadan_lantern(end_x, end_y + size * 0.15, size * 1.45)

    def _draw_ramadan_single_crescent(self, x, y, size):
        """Draw one golden crescent."""
        self.canvas.create_oval(
            x - size, y - size,
            x + size, y + size,
            fill='#d4af37',
            outline=''
        )
        self.canvas.create_oval(
            x - size + (size * 0.46), y - size + (size * 0.10),
            x + size + (size * 0.46), y + size + (size * 0.10),
            fill='#2c1169',
            outline=''
        )

    def draw_ramadan_crescents(self, width, height):
        """Draw golden crescents for Ramadan background."""
        crescent_positions = [
            (width * 0.12, height * 0.12, min(width, height) * 0.030),
            (width * 0.34, height * 0.18, min(width, height) * 0.024),
            (width * 0.68, height * 0.14, min(width, height) * 0.028),
            (width * 0.86, height * 0.22, min(width, height) * 0.022),
            (width * 0.22, height * 0.78, min(width, height) * 0.026),
            (width * 0.74, height * 0.74, min(width, height) * 0.030),
        ]

        bg_cutout = '#3a1763'
        for x, y, size in crescent_positions:
            self.canvas.create_oval(
                x - size, y - size,
                x + size, y + size,
                fill='#d4af37',
                outline=''
            )
            self.canvas.create_oval(
                x - size + (size * 0.42), y - size + (size * 0.10),
                x + size + (size * 0.42), y + size + (size * 0.10),
                fill=bg_cutout,
                outline=''
            )

    def draw_ramadan_stars(self, width, height):
        """Draw sparse golden stars (sample-like)."""
        return  # Stars disabled
        bottom_star_cutoff = 0.82
        star_points = [
            (0.08, 0.20, 1.0), (0.18, 0.28, 0.7), (0.30, 0.22, 0.9), (0.43, 0.26, 0.8),
            (0.57, 0.21, 0.6), (0.69, 0.29, 0.9), (0.82, 0.23, 1.0), (0.90, 0.31, 0.7),
            (0.10, 0.44, 1.1), (0.24, 0.47, 0.8), (0.38, 0.43, 1.0), (0.52, 0.46, 0.7),
            (0.66, 0.42, 1.0), (0.80, 0.48, 0.9), (0.13, 0.62, 1.2), (0.27, 0.67, 0.8),
            (0.41, 0.61, 1.0), (0.56, 0.66, 0.7), (0.72, 0.62, 1.1), (0.86, 0.68, 0.9),
            (0.18, 0.80, 1.0), (0.34, 0.84, 0.8), (0.52, 0.81, 1.0), (0.70, 0.86, 0.9),
            (0.84, 0.82, 1.1),
            (0.05, 0.13, 0.55), (0.14, 0.17, 1.25), (0.22, 0.14, 0.65), (0.33, 0.16, 1.35),
            (0.47, 0.15, 0.60), (0.61, 0.17, 1.30), (0.74, 0.14, 0.70), (0.88, 0.16, 1.20),
            (0.06, 0.35, 0.75), (0.17, 0.38, 1.40), (0.29, 0.36, 0.65), (0.46, 0.39, 1.25),
            (0.59, 0.34, 0.70), (0.73, 0.37, 1.30), (0.91, 0.40, 0.60),
            (0.09, 0.54, 0.65), (0.20, 0.57, 1.35), (0.35, 0.53, 0.75), (0.49, 0.56, 1.20),
            (0.63, 0.58, 0.65), (0.77, 0.55, 1.40), (0.90, 0.59, 0.70),
            (0.07, 0.73, 0.60), (0.23, 0.74, 1.30), (0.31, 0.77, 0.70), (0.46, 0.75, 1.45),
            (0.60, 0.79, 0.60), (0.75, 0.76, 1.25), (0.92, 0.72, 0.65),
            (0.12, 0.90, 1.30), (0.28, 0.92, 0.65), (0.44, 0.90, 1.20), (0.62, 0.93, 0.70),
            (0.78, 0.91, 1.35), (0.94, 0.89, 0.60)
        ]

        base_size = min(width, height) * 0.008
        for sx, sy, scale in star_points:
            if sy >= bottom_star_cutoff:
                continue
            self.draw_small_star(width * sx, height * sy, base_size * scale, '#f2d675')

    def draw_ramadan_lanterns(self, width, height):
        """Draw hanging golden lantern motifs for Ramadan."""
        lantern_specs = [
            (width * 0.10, height * 0.03, min(width, height) * 0.10),
            (width * 0.90, height * 0.03, min(width, height) * 0.10),
        ]

        for x, top_y, size in lantern_specs:
            self.draw_ramadan_lantern(x, top_y, size)

    def draw_ramadan_lantern(self, x, top_y, size, tags=None):
        """Draw a single stylized hanging lantern."""
        string_len = size * 0.55
        body_top = top_y + string_len
        body_h = size
        body_w = size * 0.52
        cap_h = size * 0.18
        foot_h = size * 0.14

        pulse_phase = ((time.time() / self.lantern_pulse_cycle_seconds) * (2 * math.pi)) + (x * 0.01)
        pulse_t = 0.5 + (0.5 * math.sin(pulse_phase))
        intensity = 0.25 + (0.75 * pulse_t)

        line_color = self._mix_hex_color('#9f8a3b', '#f2d675', intensity)
        cap_fill = self._mix_hex_color('#8a6f24', '#d4af37', intensity)
        cap_outline = self._mix_hex_color('#705820', '#b38f2c', intensity)
        ring_color = self._mix_hex_color('#9b7e2a', '#d4af37', intensity)
        body_fill = self._mix_hex_color('#a6842d', '#f0cf68', intensity)
        body_outline = self._mix_hex_color('#7a5f22', '#b38f2c', intensity)
        glow_fill = self._mix_hex_color('#7f6e3b', '#fff2b8', intensity)
        foot_fill = self._mix_hex_color('#8a6f24', '#d4af37', intensity)
        foot_outline = self._mix_hex_color('#705820', '#b38f2c', intensity)

        # Hanging line
        self.canvas.create_line(
            x,
            top_y,
            x,
            body_top,
            fill=line_color,
            width=max(1, int(size * 0.035)),
            tags=tags
        )

        # Top cap
        self.canvas.create_polygon(
            x - (body_w * 0.30), body_top,
            x + (body_w * 0.30), body_top,
            x + (body_w * 0.18), body_top + cap_h,
            x - (body_w * 0.18), body_top + cap_h,
            fill=cap_fill,
            outline=cap_outline,
            width=1,
            tags=tags
        )

        # Lantern ring
        self.canvas.create_oval(
            x - (body_w * 0.11),
            body_top - (cap_h * 0.65),
            x + (body_w * 0.11),
            body_top - (cap_h * 0.15),
            outline=ring_color,
            width=2,
            tags=tags
        )

        # Lantern body
        body_y1 = body_top + cap_h
        body_y2 = body_y1 + body_h
        self.canvas.create_polygon(
            x - (body_w * 0.50), body_y1,
            x + (body_w * 0.50), body_y1,
            x + (body_w * 0.70), (body_y1 + body_y2) / 2,
            x + (body_w * 0.45), body_y2,
            x - (body_w * 0.45), body_y2,
            x - (body_w * 0.70), (body_y1 + body_y2) / 2,
            fill=body_fill,
            outline=body_outline,
            width=2,
            tags=tags
        )

        # Inner glow window
        self.canvas.create_oval(
            x - (body_w * 0.22), body_y1 + (body_h * 0.22),
            x + (body_w * 0.22), body_y2 - (body_h * 0.22),
            fill=glow_fill,
            outline='',
            tags=tags
        )

        # Bottom foot
        self.canvas.create_polygon(
            x - (body_w * 0.20), body_y2,
            x + (body_w * 0.20), body_y2,
            x + (body_w * 0.12), body_y2 + foot_h,
            x - (body_w * 0.12), body_y2 + foot_h,
            fill=foot_fill,
            outline=foot_outline,
            width=1,
            tags=tags
        )
    
    def load_config(self):
        """Load settings from config file"""
        config_dir = self.get_config_dir()
        config_path = config_dir / 'settings.json'
        try:
            with open(config_path, 'r', encoding='utf-8') as f:
                self.config = json.load(f)
        except Exception as e:
            self._log(f"Error loading config: {e}")
            self.config = {
                "data_file": "prayer_times.csv",
                "location": "MASJID AL-SALAM",
                "prayernow": 3,
                "shrouqplus": 10,
                "shrooqends": 15,
                "showbackgroundevery": 60,
                "showbackgroundduration": 5,
                "overwritebglog": "no",
                "theme": "moon",
                "arabicchangeevery": 30,
                "arabicnameduration": 5,
                "Eid Salah": "Eid Fitr Salah at 9:00 AM on Friday March 27 2026\nEid Adha Salah at 9:00 AM on Wednesday May 27 2027"
            }

        # Eid salah schedule lines (one per line):
        #   <Label> at <h:mm AM/PM> on <Weekday> <Month> <DD> <YYYY>
        default_eid_salah = (
            "Eid Fitr Salah at 9:00 AM on Friday March 27 2026\n"
            "Eid Adha Salah at 9:00 AM on Wednesday May 27 2027"
        )
        self.config['Eid Salah'] = str(self.config.get('Eid Salah', self.config.get('eidsalah', default_eid_salah)) or '').strip()
        self.config['ArafahTakbeerstart'] = str(self.config.get('ArafahTakbeerstart', '') or '').strip()
        self.config['ArafahTakbeerend'] = str(self.config.get('ArafahTakbeerend', '') or '').strip()
        try:
            self.arafah_takbeer_display_seconds = max(1, int(self.config.get('ArafahTakbeerDisplaySeconds', 3)))
        except:
            self.arafah_takbeer_display_seconds = 3
        try:
            # Interpreted as full cycle interval: panel appears every N seconds.
            self.arafah_takbeer_pause_seconds = max(1, int(self.config.get('ArafahTakbeerPauseSeconds', 15)))
        except:
            self.arafah_takbeer_pause_seconds = 15
        self.config['ArafahTakbeerDisplaySeconds'] = self.arafah_takbeer_display_seconds
        self.config['ArafahTakbeerPauseSeconds'] = self.arafah_takbeer_pause_seconds
        show_takbeer_panel_val = str(self.config.get('ArafahTakbeerPanel', 'yes')).strip().lower()
        self.show_arafah_takbeer_panel = show_takbeer_panel_val in ('yes', 'true', '1')
        self.config['ArafahTakbeerPanel'] = 'yes' if self.show_arafah_takbeer_panel else 'no'
        show_takbeer_shower_val = str(self.config.get('TakbeerShower', 'yes')).strip().lower()
        self.show_takbeer_shower = show_takbeer_shower_val in ('yes', 'true', '1')
        self.config['TakbeerShower'] = 'yes' if self.show_takbeer_shower else 'no'
        self.arafah_takbeer_start_date = self._parse_config_date(self.config['ArafahTakbeerstart'])
        self.arafah_takbeer_end_date = self._parse_config_date(self.config['ArafahTakbeerend'])
        self._reset_arafah_takbeer_cycle()

        # Visual theme selection
        theme_name = str(self.config.get('theme', 'moon')).strip().lower()
        if theme_name in ('elegent_v2', 'elegent v2', 'elegent v2.0', 'elegent_v2.0', 'elegant_v2', 'elegant v2', 'elegant v2.0', 'elegant_v2.0'):
            theme_name = 'elegent_v2'
        elif theme_name in ('elegent', 'elegant'):
            theme_name = 'modern'
        if theme_name not in ('moon', 'modern', 'ramadan', 'elegent', 'elegent_v2'):
            theme_name = 'moon'
        self.config['theme'] = theme_name

        # Optional full-screen background image path
        self.config['background_image'] = str(self.config.get('background_image', '')).strip()

        # Periodic background-image reveal settings.
        # showbackgroundevery=0 disables periodic background image display entirely.
        try:
            show_background_every = int(self.config.get('showbackgroundevery', 60))
            show_background_every = max(0, show_background_every)
        except:
            show_background_every = 60
        try:
            show_background_duration = int(self.config.get('showbackgroundduration', 5))
            show_background_duration = max(0, show_background_duration)
        except:
            show_background_duration = 5
        self.config['showbackgroundevery'] = show_background_every
        self.config['showbackgroundduration'] = show_background_duration
        self.show_background_every_seconds = show_background_every
        self.show_background_duration_seconds = show_background_duration
        if not hasattr(self, '_background_cycle_started_mono'):
            self._background_cycle_started_mono = time.monotonic()

        # Post-prayer overlay duration in minutes (configurable)
        try:
            prayernow_minutes = int(self.config.get('prayernow', 3))
            prayernow_minutes = max(0, prayernow_minutes)
        except:
            prayernow_minutes = 3
        self.config['prayernow'] = prayernow_minutes
        self.iqamah_post_duration_seconds = prayernow_minutes * 60

        # Athan callout duration. For convenience, values <= 60 are treated
        # as minutes (e.g., 15 means 15 minutes). Larger values are treated
        # as seconds for backward compatibility.
        try:
            athan_blink_duration = int(self.config.get('athancalloutduran', 25))
            athan_blink_duration = max(0, athan_blink_duration)
        except:
            athan_blink_duration = 25
        self.config['athancalloutduran'] = athan_blink_duration

        # Arabic prayer-name display cadence in seconds (English by default)
        try:
            arabic_change_every_seconds = int(self.config.get('arabicchangeevery', 30))
            arabic_change_every_seconds = max(1, arabic_change_every_seconds)
        except:
            arabic_change_every_seconds = 30
        self.config['arabicchangeevery'] = arabic_change_every_seconds

        try:
            arabic_name_duration_seconds = int(self.config.get('arabicnameduration', 10))
            arabic_name_duration_seconds = max(0, arabic_name_duration_seconds)
        except:
            arabic_name_duration_seconds = 5
        arabic_name_duration_seconds = min(arabic_name_duration_seconds, arabic_change_every_seconds)
        self.config['arabicnameduration'] = arabic_name_duration_seconds

        # Shrouq additional minutes label (configurable)
        try:
            shrouq_plus_minutes = int(self.config.get('shrouqplus', 10))
            shrouq_plus_minutes = max(0, shrouq_plus_minutes)
        except:
            shrouq_plus_minutes = 10
        self.config['shrouqplus'] = shrouq_plus_minutes

        # Shrouq end buffer in minutes before Duhr/Jummah where no prayer is highlighted.
        try:
            shrooq_ends_minutes = int(self.config.get('shrooqends', 15))
            shrooq_ends_minutes = max(0, shrooq_ends_minutes)
        except:
            shrooq_ends_minutes = 15
        self.config['shrooqends'] = shrooq_ends_minutes
        self.shrooq_ends_minutes = shrooq_ends_minutes

        # Red prayer-change ribbon visibility timings (seconds)
        try:
            red_ribbon_show_seconds = int(self.config.get('redribbonshow', 15))
            red_ribbon_show_seconds = max(1, red_ribbon_show_seconds)
        except:
            red_ribbon_show_seconds = 15
        try:
            red_ribbon_hide_seconds = int(self.config.get('redribbonhide', 45))
            red_ribbon_hide_seconds = max(1, red_ribbon_hide_seconds)
        except:
            red_ribbon_hide_seconds = 45
        self.config['redribbonshow'] = red_ribbon_show_seconds
        self.config['redribbonhide'] = red_ribbon_hide_seconds
        self.red_ribbon_show_seconds = red_ribbon_show_seconds
        self.red_ribbon_hide_seconds = red_ribbon_hide_seconds
        self.config['khutbahoverlayendsat'] = str(self.config.get('khutbahoverlayendsat', '2:00 PM') or '2:00 PM').strip()

        # Show logs (console print output) - default No
        showlogs_val = str(self.config.get('showlogs', 'no')).strip().lower()
        self.show_logs = showlogs_val in ('yes', 'true', '1')

        # Show logo images - default No
        showlogo_val = str(self.config.get('showlogo', 'no')).strip().lower()
        self.show_logo = showlogo_val in ('yes', 'true', '1')

        # News tape hide duration in seconds (0 = never hide)
        try:
            hide_tape = int(self.config.get('hidenewstape', 30))
            hide_tape = max(0, hide_tape)
        except:
            hide_tape = 30
        self.news_tape_hide_duration = hide_tape

        # Overlay opacity for iqamah countdown & prayer now (12, 25, 50, 75)
        try:
            opacity_val = int(self.config.get('countandprayeropacity', 50))
        except:
            opacity_val = 50
        stipple_map = {12: 'gray12', 25: 'gray25', 50: 'gray50', 75: 'gray75'}
        # Snap to nearest valid stipple
        nearest = min(stipple_map.keys(), key=lambda k: abs(k - opacity_val))
        self.overlay_stipple = stipple_map[nearest]
        self.overlay_opacity_percent = max(0, min(100, opacity_val))

        # Prayer box opacity (100=solid, 75/50/25/12=semi-transparent)
        try:
            box_opacity_val = int(self.config.get('prayerboxopacity', 100))
        except:
            box_opacity_val = 100
        if box_opacity_val >= 100:
            self.prayer_box_stipple = ''
        else:
            box_nearest = min(stipple_map.keys(), key=lambda k: abs(k - box_opacity_val))
            self.prayer_box_stipple = stipple_map[box_nearest]
        self.prayer_box_opacity_percent = max(0, min(100, box_opacity_val))

        # Announcement ribbon background color
        self.announcement_bg_color = str(self.config.get('announcementbgcolor', '#0a1128')).strip()

        # Show weather display - default No
        showweather_val = str(self.config.get('showweather', 'no')).strip().lower()
        self.show_weather = showweather_val in ('yes', 'true', '1')
        
        # Load location/address from address.txt if available
        address_path = config_dir / 'address.txt'
        try:
            if address_path.exists():
                with open(address_path, 'r', encoding='utf-8') as f:
                    address = f.read().strip()
                    if address:
                        self.config['location'] = address
        except Exception as e:
            self._log(f"Error loading address: {e}")
        
        # Load masjid name from masjid.txt if available
        masjid_path = config_dir / 'masjid.txt'
        try:
            if masjid_path.exists():
                with open(masjid_path, 'r', encoding='utf-8') as f:
                    masjid_name = f.read().strip()
                    if masjid_name:
                        self.config['masjid_name'] = masjid_name
        except Exception as e:
            self._log(f"Error loading masjid name: {e}")

    def get_config_dir(self):
        """Resolve config directory from runtime location, cwd, then source location."""
        candidates = []

        if getattr(sys, 'frozen', False):
            exe_dir = Path(sys.executable).resolve().parent
            candidates.append(exe_dir.parent / 'config')
            candidates.append(exe_dir / 'config')

        candidates.append(Path.cwd() / 'config')
        candidates.append(Path(__file__).resolve().parent / 'config')

        for candidate in candidates:
            if candidate.exists() and candidate.is_dir():
                return candidate

        return Path(__file__).resolve().parent / 'config'

    def _load_background_log(self):
        """Load the background image log from config/background_log.json."""
        log_path = self.get_config_dir() / 'background_log.json'
        try:
            if log_path.exists():
                with open(log_path, 'r', encoding='utf-8') as f:
                    return json.load(f)
        except Exception as e:
            self._log(f"Error loading background log: {e}")
        return {"shown": {}}

    def _save_background_log(self, log_data):
        """Save the background image log to config/background_log.json.
        When overwritebglog is 'no', merge new entries with existing local log
        instead of overwriting, protecting against remote/bundled overwrites."""
        log_path = self.get_config_dir() / 'background_log.json'
        try:
            overwrite = str(self.config.get('overwritebglog', 'no')).strip().lower()
            if overwrite == 'no' and log_path.exists():
                # Merge: keep existing entries, add/update new ones
                try:
                    with open(log_path, 'r', encoding='utf-8') as f:
                        existing = json.load(f)
                    existing_shown = existing.get('shown', {})
                    new_shown = log_data.get('shown', {})
                    # If new log has fewer entries (e.g. reset cycle), use new log
                    if len(new_shown) >= len(existing_shown):
                        existing_shown.update(new_shown)
                        log_data['shown'] = existing_shown
                    # else: full reset intended, use new_shown as-is
                except:
                    pass
            with open(log_path, 'w', encoding='utf-8') as f:
                json.dump(log_data, f, indent=2)
        except Exception as e:
            self._log(f"Error saving background log: {e}")

    def get_background_image_path(self):
        """Resolve background image path. Picks one image per day using a persistent log.
        Every image is shown once before any repeats. Log resets when all shown."""
        bg_folder = Path(__file__).resolve().parent / 'images' / 'background'
        # Prefer external images folder (next to exe or cwd) for frozen builds
        if getattr(sys, 'frozen', False):
            ext_bg = Path(sys.executable).resolve().parent.parent / 'images' / 'background'
            if not ext_bg.is_dir():
                ext_bg = Path(sys.executable).resolve().parent / 'images' / 'background'
            if ext_bg.is_dir():
                bg_folder = ext_bg
        else:
            cwd_bg = Path.cwd() / 'images' / 'background'
            if cwd_bg.is_dir():
                bg_folder = cwd_bg

        if bg_folder.is_dir():
            # Check for manual override (only on the specified date)
            override = str(self.config.get('background_override', '')).strip()
            override_date = str(self.config.get('background_override_date', '')).strip()
            if override:
                use_override = True
                if override_date:
                    today_str = self.get_current_date().strftime('%Y-%m-%d')
                    use_override = (today_str == override_date)
                if use_override:
                    override_path = bg_folder / override
                    if override_path.is_file():
                        return override_path.resolve()

            bg_images = sorted([
                f for f in bg_folder.iterdir()
                if f.is_file() and f.suffix.lower() in ('.png', '.jpg', '.jpeg', '.bmp', '.gif')
            ])
            if bg_images:
                today_str = self.get_current_date().strftime('%Y-%m-%d')
                log_data = self._load_background_log()
                shown = log_data.get("shown", {})

                # If today already has an entry, return that image — never overwrite it
                for img_name, date_shown in shown.items():
                    if date_shown == today_str:
                        match = next((f for f in bg_images if f.name == img_name), None)
                        if match:
                            return match.resolve()

                # No entry for today yet — pick one and log it
                all_names = {f.name for f in bg_images}
                shown_names = set(shown.keys())
                remaining = all_names - shown_names

                # All shown — reset cycle and start fresh
                if not remaining:
                    shown = {}
                    remaining = all_names

                # Pick a random image from remaining
                chosen_name = random.choice(sorted(remaining))
                chosen_path = next(f for f in bg_images if f.name == chosen_name)

                # Log it (only once per day — restarts will hit the guard above)
                shown[chosen_name] = today_str
                log_data["shown"] = shown
                self._save_background_log(log_data)

                return chosen_path.resolve()

        # Fallback to configured background_image setting
        image_setting = str(self.config.get('background_image', '')).strip()
        if not image_setting:
            return None

        configured_path = Path(image_setting)
        candidates = []

        if configured_path.is_absolute():
            candidates.append(configured_path)
        else:
            config_dir = self.get_config_dir()
            app_dir = Path(__file__).resolve().parent
            candidates.extend([
                config_dir / configured_path,
                Path.cwd() / configured_path,
                app_dir / configured_path,
            ])
            if configured_path.parent == Path('.'):
                candidates.append(app_dir / 'images' / configured_path.name)

        for candidate in candidates:
            if candidate.exists() and candidate.is_file():
                return candidate.resolve()

        self._log(f"Warning: background image not found: {image_setting}")
        return None

    def draw_background_image(self, width, height):
        """Draw a configured background image stretched to full canvas."""
        image_path = self.get_background_image_path()
        if image_path is None:
            return False

        image_path_str = str(image_path)
        if self.background_image_path != image_path_str:
            try:
                self.background_base_image = Image.open(image_path_str).convert('RGB')
                self.background_image_path = image_path_str
                self.background_image_size = (0, 0)
                self.background_photo_image = None
            except Exception as e:
                self._log(f"Warning: unable to load background image '{image_path_str}': {e}")
                self.background_base_image = None
                self.background_photo_image = None
                self.background_image_size = (0, 0)
                self.background_image_path = None
                return False

        if self.background_base_image is None:
            return False

        if self.background_image_size != (width, height) or self.background_photo_image is None:
            try:
                if hasattr(Image, 'Resampling'):
                    resized = self.background_base_image.resize((width, height), Image.Resampling.LANCZOS)
                else:
                    resized = self.background_base_image.resize((width, height), Image.LANCZOS)

                self.background_photo_image = ImageTk.PhotoImage(resized)
                self.background_image_size = (width, height)
            except Exception as e:
                self._log(f"Warning: unable to resize background image '{image_path_str}': {e}")
                return False

        self.canvas.create_image(0, 0, image=self.background_photo_image, anchor='nw')
        return True

    def draw_background_image_label(self, width, height, tags=()):
        """Draw masjid name and location label on the background image.
        
        Filename format: 'Name - Location.ext' => name on top, location below with decorative lines.
        """
        image_path = self.get_background_image_path()
        if image_path is None:
            return

        stem = Path(str(image_path)).stem
        if stem.lower() == 'unknown masjid':
            return

        # Parse "Name - Location" from filename
        if ' - ' in stem:
            name_part, location_part = stem.rsplit(' - ', 1)
        else:
            name_part = stem
            location_part = ''

        cx = width // 2
        label_shift_up = self.us(28, 14) if ('iqamah_overlay' in str(tags)) else 0
        top_y = height - self.us(170, 85) - label_shift_up

        # Masjid name - large italic serif
        name_font = ('Georgia', self.fs(48, 24), 'bold italic')
        self.draw_outlined_text(
            cx, top_y, name_part,
            font=name_font, fill='white', outline='black', outline_px=3,
            anchor='center', tags=tags
        )

        if location_part:
            loc_y = top_y + self.us(50, 25)
            loc_font = ('Arial', self.fs(30, 15), 'bold')
            loc_text = location_part.upper()

            # Measure location text width for decorative lines
            tmp_id = self.canvas.create_text(0, 0, text=loc_text, font=loc_font)
            bbox = self.canvas.bbox(tmp_id)
            self.canvas.delete(tmp_id)
            text_w = (bbox[2] - bbox[0]) if bbox else self.us(120, 60)

            line_len = self.us(60, 30)
            line_gap = self.us(16, 8)
            line_y = loc_y

            # Left decorative line
            self.canvas.create_line(
                cx - text_w // 2 - line_gap - line_len, line_y,
                cx - text_w // 2 - line_gap, line_y,
                fill='white', width=self.us(2, 1), tags=tags
            )
            # Right decorative line
            self.canvas.create_line(
                cx + text_w // 2 + line_gap, line_y,
                cx + text_w // 2 + line_gap + line_len, line_y,
                fill='white', width=self.us(2, 1), tags=tags
            )

            # Location text
            self.draw_outlined_text(
                cx, loc_y, loc_text,
                font=loc_font, fill='white', outline='black', outline_px=2,
                anchor='center', tags=tags
            )

    def draw_overlay_background(self, width, height, tags='iqamah_overlay'):
        """Draw configured background image for full-screen overlays; fallback to solid fill."""
        image_path = self.get_background_image_path()
        if image_path is not None:
            image_path_str = str(image_path)
            if self.background_image_path != image_path_str:
                try:
                    self.background_base_image = Image.open(image_path_str).convert('RGB')
                    self.background_image_path = image_path_str
                    self.background_image_size = (0, 0)
                    self.background_photo_image = None
                except Exception as e:
                    self._log(f"Warning: unable to load background image '{image_path_str}': {e}")
                    self.background_base_image = None
                    self.background_photo_image = None
                    self.background_image_size = (0, 0)
                    self.background_image_path = None

            if self.background_base_image is not None:
                if self.background_image_size != (width, height) or self.background_photo_image is None:
                    try:
                        if hasattr(Image, 'Resampling'):
                            resized = self.background_base_image.resize((width, height), Image.Resampling.LANCZOS)
                        else:
                            resized = self.background_base_image.resize((width, height), Image.LANCZOS)
                        self.background_photo_image = ImageTk.PhotoImage(resized)
                        self.background_image_size = (width, height)
                    except Exception as e:
                        self._log(f"Warning: unable to resize background image '{image_path_str}': {e}")
                        self.background_photo_image = None

                if self.background_photo_image is not None:
                    return self.canvas.create_image(
                        0, 0,
                        image=self.background_photo_image,
                        anchor='nw',
                        tags=tags
                    )

        return self.canvas.create_rectangle(
            -2, -2, width + 2, height + 2,
            fill='#f2f2f2',
            outline='',
            tags=tags
        )

    def get_theme_name(self):
        """Get normalized theme name from config."""
        theme_name = str(self.config.get('theme', 'moon')).strip().lower()
        if theme_name in ('elegent_v2', 'elegent v2', 'elegent v2.0', 'elegent_v2.0', 'elegant_v2', 'elegant v2', 'elegant v2.0', 'elegant_v2.0'):
            return 'elegent_v2'
        if theme_name in ('elegent', 'elegant'):
            return 'modern'
        if theme_name not in ('moon', 'modern', 'ramadan', 'elegent', 'elegent_v2'):
            return 'moon'
        return theme_name

    def get_theme_palette(self):
        """Return rendering colors for the selected theme."""
        theme_name = self.get_theme_name()
        if theme_name == 'modern':
            return {
                'card_fill': '#0f2d66',
                'card_outline': '#4f75c0',
                'card_current_fill': '#2a56ad',
                'card_current_outline': '#d4af37',
                'title_text': '#f2f7ff',
                'subtle_text': '#b7c8ee',
                'athan_text': '#f8fbff',
                'iqamah_text': '#bfead2',
                'shrouq_note_text': '#97d9b8',
                'next_panel_fill': '#ffffff',
                'next_panel_outline': '#334155',
                'next_prefix_text': '#0f172a',
                'next_name_text': '#b91c1c',
                'next_in_text': '#0f172a',
                'next_countdown_text': '#047857',
                'header_line': '#14b8a6',
                'verse_box': '#0f172a',
                'build_info_text': '#e2e8f0'
            }

        if theme_name == 'elegent':
            return {
                'card_fill': '#fdfaf2',
                'card_outline': '#8b6b2e',
                'card_current_fill': '#ffe082',
                'card_current_outline': '#d4af37',
                'title_text': '#2c1f12',
                'subtle_text': '#6b4f2a',
                'athan_text': '#2c1f12',
                'iqamah_text': '#1f6b4f',
                'shrouq_note_text': '#2e7d32',
                'next_panel_fill': '#fff9ec',
                'next_panel_outline': '#8b6b2e',
                'next_prefix_text': '#2c1f12',
                'next_name_text': '#9b2226',
                'next_in_text': '#2c1f12',
                'next_countdown_text': '#1f6b4f',
                'header_line': '#c39b45',
                'verse_box': '#1e2742',
                'build_info_text': '#f4ecd9'
            }

        if theme_name == 'elegent_v2':
            return {
                'card_fill': '#0d2a66',
                'card_alt_fill': '#8fc4ff',
                'card_outline': '#3a5ea8',
                'card_current_fill': '#d4af37',
                'card_current_outline': '#9ec5ff',
                'title_text': '#eef5ff',
                'subtle_text': '#c8dbff',
                'athan_text': '#f5f9ff',
                'iqamah_text': '#d9eaff',
                'shrouq_note_text': '#2e7d32',
                'next_panel_fill': '#fff8e8',
                'next_panel_outline': '#8a6a2b',
                'next_prefix_text': '#2b1d0e',
                'next_name_text': '#8f1d1d',
                'next_in_text': '#2b1d0e',
                'next_countdown_text': '#165f3f',
                'header_line': '#c9a24f',
                'verse_box': '#1e2742',
                'build_info_text': '#f4ecd9'
            }

        return {
            'card_fill': '#0f2d66',
            'card_outline': '#4f75c0',
            'card_current_fill': '#2a56ad',
            'card_current_outline': '#d4af37',
            'title_text': '#f2f7ff',
            'subtle_text': '#b7c8ee',
            'athan_text': '#f8fbff',
            'iqamah_text': '#bfead2',
            'shrouq_note_text': '#97d9b8',
            'next_panel_fill': 'white',
            'next_panel_outline': '#2a5a8f',
            'next_prefix_text': 'black',
            'next_name_text': '#d32f2f',
            'next_in_text': 'black',
            'next_countdown_text': '#2E7D32',
            'header_line': '#2a5a8f',
            'verse_box': '#1a3a5a',
            'build_info_text': 'white'
        }
    
    def draw_background_ornaments(self, width, height):
        """Draw large decorative circular patterns in background"""
        # Disabled per UI request.
        return
    
    def is_ramadan(self, date_obj):
        """Check if a Gregorian date falls in Ramadan (Hijri month 9)."""
        try:
            hijri_date = Gregorian(date_obj.year, date_obj.month, date_obj.day).to_hijri()
            return hijri_date.month == 9
        except:
            # Fallback date window for 2026 if Hijri conversion fails
            try:
                ramadan_start = datetime.strptime('2026-02-18', '%Y-%m-%d').date()
                ramadan_end = datetime.strptime('2026-03-29', '%Y-%m-%d').date()
                return ramadan_start <= date_obj <= ramadan_end
            except:
                return False

    def is_eid_day(self, date_obj):
        """Check if date is Eid al-Fitr (1 Shawwal) or Eid al-Adha (10 Dhul-Hijjah)."""
        try:
            hijri_date = Gregorian(date_obj.year, date_obj.month, date_obj.day).to_hijri()
            return (hijri_date.month == 10 and hijri_date.day == 1) or (hijri_date.month == 12 and hijri_date.day == 10)
        except:
            # Fallback windows for 2026 if Hijri conversion is unavailable.
            return date_obj in {
                datetime.strptime('2026-03-30', '%Y-%m-%d').date(),  # Eid al-Fitr 2026
                datetime.strptime('2026-05-27', '%Y-%m-%d').date()   # Eid al-Adha 2026
            }

    def draw_eid_background(self, width, height):
        """Draw Eid-only celebratory background with fireworks and balloons."""
        gradient_steps = 54
        top_r, top_g, top_b = (20, 38, 82)
        bot_r, bot_g, bot_b = (54, 95, 169)

        for i in range(gradient_steps):
            ratio = i / max(1, gradient_steps - 1)
            r = int(top_r + (bot_r - top_r) * ratio)
            g = int(top_g + (bot_g - top_g) * ratio)
            b = int(top_b + (bot_b - top_b) * ratio)
            color = f'#{r:02x}{g:02x}{b:02x}'
            y_pos = (height * i) / gradient_steps
            self.canvas.create_rectangle(
                0, y_pos, width, y_pos + (height / gradient_steps) + 2,
                fill=color,
                outline=''
            )

        self.draw_eid_galaxy(width, height)
        self.draw_eid_upper_glow_decor(width, height)

    def draw_eid_galaxy(self, width, height):
        """Draw a Milky Way-like band with stars and planets."""
        band_layers = [
            (0.50, 0.26, 0.98, 0.36, '#1f2f74'),
            (0.52, 0.27, 0.86, 0.28, '#2b3f8e'),
            (0.49, 0.28, 0.72, 0.22, '#3c4da0'),
            (0.53, 0.29, 0.56, 0.16, '#6f6fc4')
        ]

        for cx_r, cy_r, w_r, h_r, color in band_layers:
            cx = width * cx_r
            cy = height * cy_r
            band_w = width * w_r
            band_h = height * h_r
            self.canvas.create_oval(
                cx - (band_w / 2), cy - (band_h / 2),
                cx + (band_w / 2), cy + (band_h / 2),
                fill=color,
                outline=''
            )

        stars = [
            (0.04, 0.10, 1.00, '#e7f0ff'), (0.08, 0.14, 0.85, '#d8e8ff'), (0.12, 0.08, 1.10, '#f4f8ff'), (0.16, 0.12, 0.90, '#d8e8ff'),
            (0.20, 0.09, 1.05, '#f4f8ff'), (0.24, 0.15, 0.80, '#d8e8ff'), (0.28, 0.10, 0.95, '#e7f0ff'), (0.32, 0.13, 0.85, '#d8e8ff'),
            (0.36, 0.08, 1.15, '#f4f8ff'), (0.40, 0.14, 0.90, '#e7f0ff'), (0.44, 0.09, 0.85, '#d8e8ff'), (0.48, 0.13, 1.00, '#f4f8ff'),
            (0.52, 0.09, 0.95, '#e7f0ff'), (0.56, 0.14, 0.85, '#d8e8ff'), (0.60, 0.08, 1.10, '#f4f8ff'), (0.64, 0.12, 0.90, '#d8e8ff'),
            (0.68, 0.10, 0.95, '#e7f0ff'), (0.72, 0.14, 0.80, '#d8e8ff'), (0.76, 0.08, 1.05, '#f4f8ff'), (0.80, 0.12, 0.90, '#e7f0ff'),
            (0.84, 0.09, 0.85, '#d8e8ff'), (0.88, 0.13, 1.00, '#f4f8ff'), (0.92, 0.08, 0.95, '#e7f0ff'), (0.96, 0.12, 0.80, '#d8e8ff'),
            (0.07, 0.21, 1.10, '#f4f8ff'), (0.13, 0.24, 0.90, '#d8e8ff'), (0.19, 0.20, 0.95, '#e7f0ff'), (0.25, 0.23, 0.80, '#d8e8ff'),
            (0.31, 0.19, 1.05, '#f4f8ff'), (0.37, 0.22, 0.85, '#e7f0ff'), (0.43, 0.20, 0.90, '#d8e8ff'), (0.49, 0.24, 1.00, '#f4f8ff'),
            (0.55, 0.19, 0.85, '#d8e8ff'), (0.61, 0.22, 0.95, '#e7f0ff'), (0.67, 0.20, 1.05, '#f4f8ff'), (0.73, 0.24, 0.85, '#d8e8ff'),
            (0.79, 0.19, 0.90, '#e7f0ff'), (0.85, 0.23, 0.80, '#d8e8ff'), (0.91, 0.21, 1.00, '#f4f8ff'),
            (0.10, 0.31, 0.90, '#d8e8ff'), (0.18, 0.34, 1.00, '#f4f8ff'), (0.26, 0.30, 0.85, '#e7f0ff'), (0.34, 0.33, 0.90, '#d8e8ff'),
            (0.42, 0.30, 1.05, '#f4f8ff'), (0.50, 0.35, 0.95, '#e7f0ff'), (0.58, 0.31, 0.90, '#d8e8ff'), (0.66, 0.34, 1.00, '#f4f8ff'),
            (0.74, 0.30, 0.85, '#e7f0ff'), (0.82, 0.33, 0.90, '#d8e8ff'), (0.90, 0.31, 1.05, '#f4f8ff')
        ]
        lower_stars = [
            (0.08, 0.58, 0.75, '#d8e8ff'), (0.14, 0.63, 1.10, '#f4f8ff'), (0.22, 0.60, 0.90, '#e7f0ff'),
            (0.30, 0.66, 1.25, '#f4f8ff'), (0.38, 0.61, 0.80, '#d8e8ff'), (0.46, 0.68, 1.05, '#e7f0ff'),
            (0.54, 0.62, 0.85, '#d8e8ff'), (0.62, 0.69, 1.20, '#f4f8ff'), (0.70, 0.61, 0.90, '#e7f0ff'),
            (0.78, 0.67, 1.15, '#f4f8ff'), (0.86, 0.60, 0.80, '#d8e8ff'), (0.93, 0.65, 1.00, '#e7f0ff'),
            (0.06, 0.75, 0.90, '#e7f0ff'), (0.16, 0.81, 1.30, '#f4f8ff'), (0.26, 0.76, 0.85, '#d8e8ff'),
            (0.36, 0.84, 1.10, '#f4f8ff'), (0.46, 0.78, 0.95, '#e7f0ff'), (0.56, 0.86, 1.35, '#f4f8ff'),
            (0.66, 0.79, 0.90, '#d8e8ff'), (0.76, 0.85, 1.20, '#f4f8ff'), (0.86, 0.77, 0.80, '#e7f0ff'),
            (0.94, 0.83, 1.05, '#d8e8ff'), (0.10, 0.91, 1.25, '#f4f8ff'), (0.24, 0.88, 0.85, '#d8e8ff'),
            (0.38, 0.93, 1.15, '#f4f8ff'), (0.52, 0.89, 0.95, '#e7f0ff'), (0.66, 0.94, 1.30, '#f4f8ff'),
            (0.80, 0.90, 0.90, '#d8e8ff'), (0.92, 0.95, 1.10, '#f4f8ff')
        ]
        self.draw_eid_star_fields(width, height, animated=False, tags=None, upper_stars=stars, lower_stars=lower_stars)

        planets = [
            (0.14, 0.20, self.us(34, 18), '#d4a574', '#c08a55'),
            (0.78, 0.18, self.us(42, 22), '#8fd2e8', '#6ab7cf'),
            (0.58, 0.33, self.us(26, 14), '#c8b5ff', '#ab93ea')
        ]

        for px_r, py_r, radius, planet_color, shade_color in planets:
            cx = width * px_r
            cy = height * py_r
            self.canvas.create_oval(
                cx - radius, cy - radius,
                cx + radius, cy + radius,
                fill=planet_color,
                outline=''
            )
            self.canvas.create_oval(
                cx - (radius * 0.2), cy - (radius * 0.2),
                cx + (radius * 0.9), cy + (radius * 0.9),
                fill=shade_color,
                outline=''
            )

        ring_planet_x = width * 0.33
        ring_planet_y = height * 0.18
        ring_planet_r = self.us(30, 16)
        self.canvas.create_oval(
            ring_planet_x - ring_planet_r, ring_planet_y - ring_planet_r,
            ring_planet_x + ring_planet_r, ring_planet_y + ring_planet_r,
            fill='#f0cf84',
            outline=''
        )
        self.canvas.create_oval(
            ring_planet_x - (ring_planet_r * 1.55), ring_planet_y - (ring_planet_r * 0.50),
            ring_planet_x + (ring_planet_r * 1.55), ring_planet_y + (ring_planet_r * 0.50),
            outline='#d8c7a0',
            width=self.us(3, 2)
        )

    def draw_eid_star_fields(self, width, height, animated=False, tags=None, upper_stars=None, lower_stars=None):
        """Draw galaxy star fields, optionally animated for glow/dim/lighten."""
        return  # Stars disabled
        bottom_star_cutoff = 0.82
        exclusion_rects = []
        bounds = getattr(self, 'prayer_box_bounds', {}) or {}
        star_padding = self.us(18, 10)
        for _, (bx, by, bw, bh) in bounds.items():
            exclusion_rects.append((bx - star_padding, by - star_padding, bx + bw + star_padding, by + bh + star_padding))

        next_panel_bounds = getattr(self, 'next_prayer_panel_bounds', None)
        if next_panel_bounds:
            bx, by, bw, bh = next_panel_bounds
            exclusion_rects.append((bx - star_padding, by - star_padding, bx + bw + star_padding, by + bh + star_padding))

        if upper_stars is None:
            upper_stars = [
                (0.04, 0.50, 1.00, '#e7f0ff'), (0.08, 0.54, 0.85, '#d8e8ff'), (0.12, 0.48, 1.10, '#f4f8ff'), (0.16, 0.52, 0.90, '#d8e8ff'),
                (0.20, 0.49, 1.05, '#f4f8ff'), (0.24, 0.55, 0.80, '#d8e8ff'), (0.28, 0.50, 0.95, '#e7f0ff'), (0.32, 0.53, 0.85, '#d8e8ff'),
                (0.36, 0.48, 1.15, '#f4f8ff'), (0.40, 0.54, 0.90, '#e7f0ff'), (0.44, 0.49, 0.85, '#d8e8ff'), (0.48, 0.53, 1.00, '#f4f8ff'),
                (0.52, 0.49, 0.95, '#e7f0ff'), (0.56, 0.54, 0.85, '#d8e8ff'), (0.60, 0.48, 1.10, '#f4f8ff'), (0.64, 0.52, 0.90, '#d8e8ff'),
                (0.68, 0.50, 0.95, '#e7f0ff'), (0.72, 0.54, 0.80, '#d8e8ff'), (0.76, 0.48, 1.05, '#f4f8ff'), (0.80, 0.52, 0.90, '#e7f0ff'),
                (0.84, 0.49, 0.85, '#d8e8ff'), (0.88, 0.53, 1.00, '#f4f8ff'), (0.92, 0.48, 0.95, '#e7f0ff'), (0.96, 0.52, 0.80, '#d8e8ff'),
                (0.07, 0.61, 1.10, '#f4f8ff'), (0.13, 0.64, 0.90, '#d8e8ff'), (0.19, 0.60, 0.95, '#e7f0ff'), (0.25, 0.63, 0.80, '#d8e8ff'),
                (0.31, 0.59, 1.05, '#f4f8ff'), (0.37, 0.62, 0.85, '#e7f0ff'), (0.43, 0.60, 0.90, '#d8e8ff'), (0.49, 0.64, 1.00, '#f4f8ff'),
                (0.55, 0.59, 0.85, '#d8e8ff'), (0.61, 0.62, 0.95, '#e7f0ff'), (0.67, 0.60, 1.05, '#f4f8ff'), (0.73, 0.64, 0.85, '#d8e8ff'),
                (0.79, 0.59, 0.90, '#e7f0ff'), (0.85, 0.63, 0.80, '#d8e8ff'), (0.91, 0.61, 1.00, '#f4f8ff'),
                (0.10, 0.71, 0.90, '#d8e8ff'), (0.18, 0.74, 1.00, '#f4f8ff'), (0.26, 0.70, 0.85, '#e7f0ff'), (0.34, 0.73, 0.90, '#d8e8ff'),
                (0.42, 0.70, 1.05, '#f4f8ff'), (0.50, 0.75, 0.95, '#e7f0ff'), (0.58, 0.71, 0.90, '#d8e8ff'), (0.66, 0.74, 1.00, '#f4f8ff'),
                (0.74, 0.70, 0.85, '#e7f0ff'), (0.82, 0.73, 0.90, '#d8e8ff'), (0.90, 0.71, 1.05, '#f4f8ff')
            ]

        if lower_stars is None:
            lower_stars = [
                (0.08, 0.82, 0.75, '#d8e8ff'), (0.14, 0.87, 1.10, '#f4f8ff'), (0.22, 0.84, 0.90, '#e7f0ff'),
                (0.30, 0.90, 1.25, '#f4f8ff'), (0.38, 0.85, 0.80, '#d8e8ff'), (0.46, 0.92, 1.05, '#e7f0ff'),
                (0.54, 0.86, 0.85, '#d8e8ff'), (0.62, 0.93, 1.20, '#f4f8ff'), (0.70, 0.85, 0.90, '#e7f0ff'),
                (0.78, 0.91, 1.15, '#f4f8ff'), (0.86, 0.84, 0.80, '#d8e8ff'), (0.93, 0.89, 1.00, '#e7f0ff'),
                (0.06, 0.97, 0.90, '#e7f0ff'), (0.16, 0.98, 1.30, '#f4f8ff'), (0.26, 0.96, 0.85, '#d8e8ff'),
                (0.36, 0.99, 1.10, '#f4f8ff'), (0.46, 0.97, 0.95, '#e7f0ff'), (0.56, 0.99, 1.35, '#f4f8ff'),
                (0.66, 0.96, 0.90, '#d8e8ff'), (0.76, 0.98, 1.20, '#f4f8ff'), (0.86, 0.95, 0.80, '#e7f0ff'),
                (0.94, 0.97, 1.05, '#d8e8ff'), (0.10, 0.98, 1.25, '#f4f8ff'), (0.24, 0.96, 0.85, '#d8e8ff'),
                (0.38, 0.99, 1.15, '#f4f8ff'), (0.52, 0.97, 0.95, '#e7f0ff'), (0.66, 0.99, 1.30, '#f4f8ff'),
                (0.80, 0.96, 0.90, '#d8e8ff'), (0.92, 0.98, 1.10, '#f4f8ff')
            ]

        t_now = time.time()

        def _draw_star_group(star_list, base_size):
            for sx, sy, scale, base_color in star_list:
                if sy >= bottom_star_cutoff:
                    continue
                px = width * sx
                py = height * sy

                if any(x1 <= px <= x2 and y1 <= py <= y2 for (x1, y1, x2, y2) in exclusion_rects):
                    continue

                star_color = base_color
                if animated:
                    phase = ((t_now / self.star_twinkle_cycle_seconds) * (2 * math.pi)) + (sx * 17.0) + (sy * 11.0)
                    twinkle_t = 0.5 + (0.5 * math.sin(phase))
                    twinkle_strength = 0.28 + (0.72 * twinkle_t)
                    star_color = self._mix_hex_color('#4f5f86', base_color, twinkle_strength)

                self.draw_hd_star(
                    px,
                    py,
                    base_size * scale,
                    star_color,
                    tags=tags
                )

        _draw_star_group(upper_stars, self.us(8, 4))
        _draw_star_group(lower_stars, self.us(9, 5))

    def draw_eid_upper_glow_decor(self, width, height):
        """Draw glowing stars and crescents in the upper section."""
        return  # Stars disabled
        upper_band_y = height * 0.19

        crescents = [
            (0.20, 0.10, 0.030),
            (0.50, 0.12, 0.034),
            (0.80, 0.10, 0.030)
        ]

        for x_ratio, y_ratio, size_ratio in crescents:
            cx = width * x_ratio
            cy = height * y_ratio
            size = min(width, height) * size_ratio

            self.canvas.create_oval(
                cx - size, cy - size,
                cx + size, cy + size,
                fill='#f4e07c',
                outline=''
            )
            self.canvas.create_oval(
                cx - size + (size * 0.42), cy - size + (size * 0.10),
                cx + size + (size * 0.42), cy + size + (size * 0.10),
                fill='#233b7d',
                outline=''
            )

        stars = [
            (0.10, 0.07, 1.0), (0.15, 0.14, 0.8), (0.27, 0.05, 0.9),
            (0.39, 0.09, 0.7), (0.61, 0.07, 1.0), (0.73, 0.05, 0.9),
            (0.85, 0.14, 0.8), (0.90, 0.07, 1.0), (0.33, 0.15, 0.7),
            (0.67, 0.15, 0.7)
        ]
        star_size = min(width, height) * 0.007
        for sx, sy, scale in stars:
            if (height * sy) > upper_band_y:
                continue
            self.draw_hd_star(width * sx, height * sy, star_size * scale, '#ffe082')

    def draw_eid_fireworks(self, width, height, animated=False, tags=None):
        """Draw simplified fireworks clearly above prayer boxes."""
        bounds = getattr(self, 'prayer_box_bounds', {}) or {}
        anchor_names = ['Fajr', 'Duhr', 'Asr', 'Isha']
        anchor_centers = []
        box_top_y = None

        for name in anchor_names:
            if name not in bounds:
                continue
            x, y, w, h = bounds[name]
            anchor_centers.append(x + (w / 2))
            box_top_y = y if box_top_y is None else min(box_top_y, y)

        if len(anchor_centers) < 4 or box_top_y is None:
            box_width = self.us(320, 190)
            box_height = self.us(230, 140)
            spacing = self.us(30, 15)
            total_width = (box_width * 5) + (spacing * 4)
            start_x = (width - total_width) / 2
            center_y = (height / 2) + self.us(40, 20)
            box_top_y = center_y - (box_height / 2)
            first_box_center_x = start_x + (box_width / 2)
            second_box_center_x = first_box_center_x + box_width + spacing
            fourth_box_center_x = first_box_center_x + (box_width + spacing) * 3
            fifth_box_center_x = first_box_center_x + (box_width + spacing) * 4
            anchor_centers = [first_box_center_x, second_box_center_x, fourth_box_center_x, fifth_box_center_x]

        min_dim = min(width, height)
        high_y = box_top_y - self.us(130, 70)
        bursts = [
            (anchor_centers[0], high_y, max(self.us(66, 34), int(min_dim * 0.052)), '#ffd54f'),
            (anchor_centers[3], high_y, max(self.us(66, 34), int(min_dim * 0.052)), '#80deea')
        ]

        t_now = time.time()
        for idx, (cx, cy, base_radius, color) in enumerate(bursts):
            if animated:
                phase = ((t_now / self.eid_firework_cycle_seconds) + (idx * 0.27)) % 1.0
                pop_strength = math.sin(phase * math.pi)
                radius = base_radius * (0.50 + (0.85 * pop_strength))
                burst_color = self._mix_hex_color('#6f7ea6', color, 0.45 + (0.55 * pop_strength))
            else:
                pop_strength = 1.0
                radius = base_radius
                burst_color = color

            ray_count = 22
            for i in range(ray_count):
                angle = (2 * math.pi * i) / ray_count
                inner_r = radius * 0.14
                outer_r = radius
                x1 = cx + inner_r * math.cos(angle)
                y1 = cy + inner_r * math.sin(angle)
                x2 = cx + outer_r * math.cos(angle)
                y2 = cy + outer_r * math.sin(angle)

                self.canvas.create_line(
                    x1, y1, x2, y2,
                    fill=burst_color,
                    width=self.us(3, 2),
                    tags=tags
                )

            core_r = self.us(14, 8)
            self.canvas.create_oval(
                cx - core_r, cy - core_r,
                cx + core_r, cy + core_r,
                fill=self._mix_hex_color('#ffffff', burst_color, 0.60),
                outline='',
                tags=tags
            )

            if animated and pop_strength > 0.88:
                self.canvas.create_text(
                    cx,
                    cy - radius - self.us(22, 12),
                    text='Eid Mubarak',
                    font=('Arial', self.fs(28, 14), 'bold'),
                    fill=burst_color,
                    tags=tags
                )

    def draw_eid_balloons(self, width, height, animated=False, tags=None):
        """Draw side balloons with strings to celebrate Eid."""
        balloons = [
            (0.06, 0.84, '#ef5350', 0.02),
            (0.11, 0.75, '#ab47bc', 0.18),
            (0.16, 0.86, '#29b6f6', 0.31),
            (0.84, 0.86, '#66bb6a', 0.47),
            (0.89, 0.75, '#ffa726', 0.62),
            (0.94, 0.84, '#ec407a', 0.79)
        ]

        balloon_w = self.us(52, 30)
        balloon_h = self.us(68, 40)
        string_len = self.us(95, 55)
        t_now = time.time()

        for x_ratio, y_ratio, color, phase_offset in balloons:
            if animated:
                rise_progress = ((t_now / self.eid_balloon_cycle_seconds) + phase_offset) % 1.0
                rise_distance = height * 0.30
                sway = math.sin((t_now * 1.9) + (phase_offset * 8.0)) * self.us(12, 6)
                cx = (width * x_ratio) + sway
                cy = (height * y_ratio) - (rise_progress * rise_distance)
            else:
                cx = width * x_ratio
                cy = height * y_ratio

            self.canvas.create_oval(
                cx - (balloon_w / 2), cy - (balloon_h / 2),
                cx + (balloon_w / 2), cy + (balloon_h / 2),
                fill=color,
                outline='white',
                width=self.us(2, 1),
                tags=tags
            )

            self.canvas.create_oval(
                cx - (balloon_w * 0.18), cy - (balloon_h * 0.20),
                cx - (balloon_w * 0.02), cy - (balloon_h * 0.04),
                fill='white',
                outline='',
                tags=tags
            )

            knot_y = cy + (balloon_h / 2)
            self.canvas.create_polygon(
                cx - self.us(5, 3), knot_y,
                cx + self.us(5, 3), knot_y,
                cx, knot_y + self.us(8, 4),
                fill=color,
                outline='white',
                width=1,
                tags=tags
            )

            self.canvas.create_line(
                cx,
                knot_y + self.us(8, 4),
                cx + self.us(10, 6),
                knot_y + string_len,
                fill='white',
                width=1,
                smooth=True,
                tags=tags
            )
    
    def load_prayer_times(self):
        """Load prayer times from base CSV and override Ramadan dates with Ramadan 2026 timings"""
        # Resolve data directory: prefer external data/ folder (next to exe or cwd) over bundled
        data_dir = Path(__file__).parent / 'data'
        if getattr(sys, 'frozen', False):
            ext_data = Path(sys.executable).resolve().parent.parent / 'data'
            if not ext_data.is_dir():
                ext_data = Path(sys.executable).resolve().parent / 'data'
            if ext_data.is_dir():
                data_dir = ext_data
        else:
            cwd_data = Path.cwd() / 'data'
            if cwd_data.is_dir():
                data_dir = cwd_data

        base_csv_path = data_dir / self.config.get('data_file', 'prayer_times.csv')
        ramadan_csv_path = data_dir / 'Ramadan-prayer-timings-2026.csv'

        self.prayer_data = {}

        try:
            with open(base_csv_path, 'r', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    date = (row.get('Date') or '').strip()
                    if date:
                        self.prayer_data[date] = row

            base_count = len(self.prayer_data)

            ramadan_overrides = 0
            if ramadan_csv_path.exists():
                with open(ramadan_csv_path, 'r', encoding='utf-8') as f:
                    reader = csv.DictReader(f)
                    for row in reader:
                        date = (row.get('Date') or '').strip()
                        if not date:
                            continue

                        if self.is_ramadan(datetime.strptime(date, '%Y-%m-%d').date()):
                            # Merge Ramadan row onto base row so metadata like Notes is preserved
                            base_row = self.prayer_data.get(date, {}).copy()
                            merged_row = base_row.copy()
                            for key, value in row.items():
                                if value is not None and str(value).strip() != '':
                                    merged_row[key] = value
                            self.prayer_data[date] = merged_row
                            ramadan_overrides += 1

            self._log(f"Loaded {base_count} base prayer entries from {base_csv_path.name}")
            self._log(f"[RAMADAN] Applied {ramadan_overrides} Ramadan overrides from {ramadan_csv_path.name}")
            self._log(f"Total active prayer entries: {len(self.prayer_data)}")

        except Exception as e:
            self._log(f"Error loading prayer times: {e}")
            self.prayer_data = {}
    
    def load_jummah_time(self):
        """Load Jummah time from config/jummah.txt (authoritative source)."""
        try:
            config_dir = self.get_config_dir()
            jummah_file = config_dir / 'jummah.txt'

            if not jummah_file.exists():
                jummah_file.write_text('1:30 PM', encoding='utf-8')
                self._log("[JUMMAH] Created config/jummah.txt with default time 1:30 PM")

            jummah_time_str = jummah_file.read_text(encoding='utf-8').strip() or '1:30 PM'
            parsed_jummah = self.parse_time(jummah_time_str)

            if parsed_jummah:
                self.jummah_time = parsed_jummah
                self._log(f"[JUMMAH] Using Jummah time from config/jummah.txt: {jummah_time_str}")
            else:
                self.jummah_time = self.parse_time('1:30 PM')
                self._log(f"[JUMMAH] Invalid jummah.txt value '{jummah_time_str}', using default 1:30 PM")

        except Exception as e:
            self._log(f"[ERROR] Failed to load Jummah time: {e}")
            self.jummah_time = self.parse_time('1:30 PM')
            self._log("[JUMMAH] Using default Jummah time: 1:30 PM")
    
    def load_announcements(self):
        """Load announcements from announcements.txt (always)."""
        # Check if current date (which might be TEST_DATE) is in Ramadan
        current_date = self.get_current_date()
        is_ramadan_period = self.is_ramadan(current_date)

        config_dir = self.get_config_dir()
        announcements_path = config_dir / 'announcements.txt'
        self._log(f"[ANNOUNCEMENTS] Loading from {announcements_path}")
        if announcements_path.exists():
            self._log(f"[ANNOUNCEMENTS] Last modified: {datetime.fromtimestamp(announcements_path.stat().st_mtime)}")
        
        try:
            with open(announcements_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
                # Filter out empty lines and create announcement list with colors
                self.announcements = []  # List of (text, color) tuples
                for line in lines:
                    line = line.strip()
                    if not line:
                        continue
                    if line.startswith('#'):
                        continue
                    
                    # Parse color if specified
                    color = 'white'  # Default color
                    text = line

                    # Convert color names to hex
                    color_map = {
                        'black': '#000000',
                        'white': '#ffffff',
                        'red': '#ff0000',
                        'green': '#00ff00',
                        'blue': '#0000ff',
                        'yellow': '#ffff00',
                        'orange': '#ffa500',
                        'gray': '#808080',
                        'grey': '#808080',
                        'gold': '#d4af37',
                        'brown': '#8b5a2b'
                    }
                    
                    # Backward-compatible: "message - color red"
                    legacy_color_match = re.search(r'\s-\scolor\s+([a-zA-Z]+)\s*$', text, flags=re.IGNORECASE)
                    if legacy_color_match:
                        color_name = legacy_color_match.group(1).lower()
                        text = re.sub(r'\s-\scolor\s+[a-zA-Z]+\s*$', '', text, flags=re.IGNORECASE).strip()
                        color = color_map.get(color_name, color)

                    # New format: "message @color gold"
                    at_color_match = re.search(r'(^|\s)@color\s+([a-zA-Z]+)(?=\s|$)', text, flags=re.IGNORECASE)
                    if at_color_match:
                        color_name = at_color_match.group(2).lower()
                        text = re.sub(r'(^|\s)@color\s+[a-zA-Z]+(?=\s|$)', ' ', text, count=1, flags=re.IGNORECASE).strip()
                        color = color_map.get(color_name, color)
                    else:
                        # Also support shorthand: "message @gold"
                        color_tag_match = re.search(r'(^|\s)@([a-zA-Z]+)(?=\s|$)', text)
                        if color_tag_match:
                            color_name = color_tag_match.group(2).lower()
                            text = re.sub(r'(^|\s)@([a-zA-Z]+)(?=\s|$)', ' ', text, count=1).strip()
                            color = color_map.get(color_name, color)

                    text = re.sub(r'\s{2,}', ' ', text).strip()

                    if not text:
                        continue
                    
                    self.announcements.append((text, color))
                
                if not self.announcements:
                    self._log("[ANNOUNCEMENTS] No announcements found; red ribbon will be hidden")
                    
                self._log(f"Loaded {len(self.announcements)} announcements with colors from {announcements_path.name}")
                for text, color in self.announcements:
                    self._log(f"  - '{text}' (color: {color})")
                    
        except Exception as e:
            self._log(f"Error loading announcements: {e}")
            self.announcements = []
        
        # Initialize tracking for scrolling
        self.announcement_index = 0
        self.current_announcement = ""  # Not used anymore, kept for compatibility
    
    def get_today_prayers(self):
        """Get prayer times for today"""
        today = self.get_current_date().strftime('%Y-%m-%d')
        return self.prayer_data.get(today, {})
    
    def get_tomorrow_prayers(self):
        """Get prayer times for tomorrow"""
        tomorrow = (self.get_current_date() + timedelta(days=1)).strftime('%Y-%m-%d')
        tomorrow_data = self.prayer_data.get(tomorrow, {})
        
        return tomorrow_data
    
    def check_prayer_changes(self):
        """Check if any prayer times change tomorrow (1 day before change)"""
        # Red ribbons show only 1 day before the change
        # Changes actually happen at midnight on the change day
        self.changing_prayers = {}
        
        for prayer, change_info in self.upcoming_changes.items():
            if prayer == 'Maghrib':
                continue
            if change_info.get('days_until') == 1:  # Changes tomorrow (1 day away) - show red ribbon today
                # Store the change info for red ribbon display
                self.changing_prayers[prayer] = {
                    'today': change_info.get('old_time', '--'),
                    'tomorrow': change_info.get('new_time', '--'),
                    'today_iqama': change_info.get('old_time', '--'),
                    'tomorrow_iqama': change_info.get('new_time', '--')
                }

        # DST day-before: show the same full-box warning style on all affected prayers.
        if self.dst_change_info and self.dst_change_info.get('days_until') == 1:
            today_prayers = self.get_today_prayers()
            tomorrow_prayers = self.get_tomorrow_prayers()
            prayers_list = ['Fajr', 'Duhr', 'Asr', 'Maghrib', 'Isha']

            for prayer in prayers_list:
                if prayer == 'Maghrib':
                    continue
                today_iqama = today_prayers.get(f'{prayer}Iqama', '--') if today_prayers else '--'
                tomorrow_iqama = tomorrow_prayers.get(f'{prayer}Iqama', '--') if tomorrow_prayers else '--'

                if today_iqama != '--' and tomorrow_iqama != '--' and today_iqama != tomorrow_iqama:
                    self.changing_prayers[prayer] = {
                        'today': today_iqama,
                        'tomorrow': tomorrow_iqama,
                        'today_iqama': today_iqama,
                        'tomorrow_iqama': tomorrow_iqama
                    }
    
    def check_upcoming_changes(self):
        """Check for upcoming prayer time changes by reading Notes column in CSV"""
        self.upcoming_changes = {}
        self.dst_change_info = None
        today = self.get_current_date()
        
        # Look for ANNOUNCEMENT dates (changes happen next day or on that day)
        # To find changes 1-3 days away, check announcements 0-3 days ahead
        for days_ahead in range(0, 4):  # Check 0, 1, 2, 3 days ahead (for changes up to 3 days away)
            check_date = (today + timedelta(days=days_ahead)).strftime('%Y-%m-%d')
            check_data = self.prayer_data.get(check_date, {})
            
            if not check_data:
                continue
            
            # Read the Notes column to find documented changes (announced on this date).
            notes = (check_data.get('Notes', '') or '').strip()
            notes_lower = notes.lower()
            has_change_marker = (
                ('iqama time changes' in notes_lower) or
                ('->' in notes) or
                (
                    ('tomorrow' in notes_lower) and
                    (('iqama' in notes_lower) or ('iqamah' in notes_lower))
                )
            )
            if notes and has_change_marker:
                
                try:
                    # Get the NEXT day's data (when change takes effect)
                    next_date = (datetime.strptime(check_date, '%Y-%m-%d') + timedelta(days=1)).strftime('%Y-%m-%d')
                    next_data = self.prayer_data.get(next_date, {})
                    
                    if not next_data:
                        continue
                    
                    # Get this date's data for comparison (old times)
                    current_data = check_data
                    
                    # Parse the notes column which contains the prayer changes
                    prayers_list = ['Fajr', 'Duhr', 'Asr', 'Maghrib', 'Isha']
                    prayer_note_aliases = {
                        'Fajr': ['fajr'],
                        'Duhr': ['duhr', 'dhuhr', 'zuhr', 'zuhar'],
                        'Asr': ['asr'],
                        'Maghrib': ['maghrib', 'magrib'],
                        'Isha': ['isha', 'ishaa', "isha'a", 'esha']
                    }
                    
                    for prayer in prayers_list:
                        # Check if this prayer is mentioned in the Notes (indicating a change)
                        aliases = prayer_note_aliases.get(prayer, [prayer.lower()])
                        if any(alias in notes_lower for alias in aliases):
                            old_time = current_data.get(f'{prayer}Iqama', '--')
                            new_time = next_data.get(f'{prayer}Iqama', '--')
                            
                            # Only add if we have valid times and they're different
                            if old_time != '--' and new_time != '--' and old_time != new_time:
                                # The change takes effect on the next date
                                change_date = datetime.strptime(next_date, '%Y-%m-%d').date()
                                # Calculate days_until as days from TODAY to effective change date
                                days_until = (change_date - today).days
                                self.upcoming_changes[prayer] = {
                                    'change_date': change_date,
                                    'new_time': new_time,
                                    'old_time': old_time,
                                    'days_until': days_until
                                }
                except Exception as e:
                    pass

        self.detect_daylight_saving_change()

    def detect_daylight_saving_change(self):
        """Detect day where all prayer times shift by one hour (DST-style change)."""
        try:
            today = self.get_current_date()
            prayers_list = ['Fajr', 'Duhr', 'Asr', 'Maghrib', 'Isha']

            for days_ahead in range(0, 4):
                base_date = today + timedelta(days=days_ahead)
                next_date = base_date + timedelta(days=1)

                base_data = self.prayer_data.get(base_date.strftime('%Y-%m-%d'), {})
                next_data = self.prayer_data.get(next_date.strftime('%Y-%m-%d'), {})
                if not base_data or not next_data:
                    continue

                minute_diffs = []
                prayer_shift_hits = 0
                for prayer in prayers_list:
                    prayer_diffs = []
                    for kind in ['Athan', 'Iqama']:
                        old_time = self.parse_time(base_data.get(f'{prayer}{kind}', ''))
                        new_time = self.parse_time(next_data.get(f'{prayer}{kind}', ''))
                        if old_time and new_time:
                            old_minutes = (old_time.hour * 60) + old_time.minute
                            new_minutes = (new_time.hour * 60) + new_time.minute
                            diff_minutes = new_minutes - old_minutes
                            minute_diffs.append(diff_minutes)
                            prayer_diffs.append(diff_minutes)

                    if prayer_diffs:
                        # This prayer participates if at least one time shifts by roughly one hour.
                        if any(45 <= abs(d) <= 75 for d in prayer_diffs):
                            prayer_shift_hits += 1

                # Require broad coverage across prayers and enough parsed values.
                if len(minute_diffs) < 6:
                    continue

                if prayer_shift_hits < 4:
                    continue

                positive = [d for d in minute_diffs if d > 0]
                negative = [d for d in minute_diffs if d < 0]

                # Determine dominant shift direction.
                if len(positive) >= len(negative):
                    direction = 1
                    directional_diffs = positive
                else:
                    direction = -1
                    directional_diffs = [-d for d in negative]

                # Need most values to agree on direction and be close to one-hour shift.
                if len(directional_diffs) < max(5, int(0.7 * len(minute_diffs))):
                    continue

                near_hour = [d for d in directional_diffs if 45 <= d <= 75]
                if len(near_hour) < max(4, int(0.7 * len(directional_diffs))):
                    continue

                self.dst_change_info = {
                    'change_date': next_date,
                    'days_until': (next_date - today).days,
                    'shift_minutes': 60 * direction
                }
                return
        except Exception:
            self.dst_change_info = None

    def parse_eid_salah_entries(self):
        """Parse configured Eid salah schedule lines into datetime entries."""
        entries = []
        raw_text = str(self.config.get('Eid Salah', self.config.get('eidsalah', '')) or '')
        if not raw_text.strip():
            return entries

        patterns = [
            re.compile(
                r'^(?P<label>.+?)\s+and\s+salah\s+is\s+at\s+(?P<time>\d{1,2}:\d{2}\s*[APap][Mm])\s+on\s+'
                r'(?P<weekday>[A-Za-z]+)\s+(?P<month>[A-Za-z]+)\s+(?P<day>\d{1,2})\s+(?P<year>\d{4})$'
            ),
            re.compile(
                r'^(?P<label>.+?)\s+salah\s+is\s+at\s+(?P<time>\d{1,2}:\d{2}\s*[APap][Mm])\s+on\s+'
                r'(?P<weekday>[A-Za-z]+)\s+(?P<month>[A-Za-z]+)\s+(?P<day>\d{1,2})\s+(?P<year>\d{4})$'
            ),
            re.compile(
                r'^(?P<label>.+?)\s+at\s+(?P<time>\d{1,2}:\d{2}\s*[APap][Mm])\s+on\s+'
                r'(?P<weekday>[A-Za-z]+)\s+(?P<month>[A-Za-z]+)\s+(?P<day>\d{1,2})\s+(?P<year>\d{4})$'
            )
        ]

        for raw_line in raw_text.splitlines():
            line = raw_line.strip()
            if not line or line.startswith('#'):
                continue
            match = None
            for pattern in patterns:
                match = pattern.match(line)
                if match:
                    break
            if not match:
                continue

            label = match.group('label').strip()
            time_str = re.sub(r'\s+', ' ', match.group('time').upper()).strip()
            date_str = f"{match.group('weekday')} {match.group('month')} {int(match.group('day')):02d} {match.group('year')} {time_str}"
            try:
                salah_dt = datetime.strptime(date_str, '%A %B %d %Y %I:%M %p')
            except:
                continue

            entries.append({
                'label': label,
                'message': line,
                'salah_dt': salah_dt,
                'end_dt': salah_dt + timedelta(hours=1)
            })

        entries.sort(key=lambda e: e['salah_dt'])
        return entries

    def get_active_eid_salah_event(self):
        """Return the next Eid salah event that has not expired yet (until 1 hour after salah)."""
        now_dt = datetime.combine(self.get_current_date(), self.get_current_time())
        for event in self.parse_eid_salah_entries():
            if now_dt <= event['end_dt']:
                return event
        return None
    
    def parse_time(self, time_str):
        """Parse time string to datetime object for comparison"""
        if not time_str or time_str == '--':
            return None
        
        try:
            # Remove extra spaces
            time_str = time_str.strip()
            
            # Try parsing with AM/PM
            if 'AM' in time_str or 'PM' in time_str:
                return datetime.strptime(time_str, '%I:%M %p').time()
            else:
                # Parse as 24-hour or assume AM for times before noon
                return datetime.strptime(time_str, '%H:%M').time()
        except:
            return None

    def resolve_sunrise_time(self, prayers_data):
        """Resolve sunrise/shrouq from known column names with a safe fallback."""
        sunrise_keys = ['Sunrise', 'Shrouq', 'Shurooq', 'Shouruq', 'Sherooq']

        for key in sunrise_keys:
            value = prayers_data.get(key, '--')
            parsed = self.parse_time(value)
            if parsed:
                return value, parsed

        # Fallback: approximate sunrise as Fajr + 90 minutes if source column is missing.
        fajr_athan = self.parse_time(prayers_data.get('FajrAthan', ''))
        if fajr_athan:
            base_date = self.get_current_date()
            fallback_dt = datetime.combine(base_date, fajr_athan) + timedelta(minutes=90)
            fallback_str = fallback_dt.strftime('%I:%M %p').lstrip('0')
            return fallback_str, fallback_dt.time()

        return '--', None
    
    def _get_hijri_month_name(self, month_number):
        """Convert Hijri month number to month name"""
        hijri_months = {
            1: "Muharram",
            2: "Safar",
            3: "Rabi' al-awwal",
            4: "Rabi' al-thani",
            5: "Jumada al-awwal",
            6: "Jumada al-thani",
            7: "Rajab",
            8: "Sha'ban",
            9: "Ramadan",
            10: "Shawwal",
            11: "Dhu al-Qi'dah",
            12: "Dhu al-Hijjah"
        }
        return hijri_months.get(month_number, str(month_number))

    def get_build_info_text(self):
        """Return build timestamp text for display from config/lastupdate.tx."""
        try:
            config_dir = self.get_config_dir()
            last_update_path = config_dir / 'lastupdate.tx'

            build_source = Path(sys.executable) if getattr(sys, 'frozen', False) else Path(__file__)
            default_build_dt = datetime.fromtimestamp(build_source.stat().st_mtime)
            default_line = default_build_dt.strftime('%Y-%m-%d %I:%M %p')

            if not last_update_path.exists():
                last_update_path.write_text(default_line + '\n', encoding='utf-8')
                return f"Build: {default_line}"

            lines = [line.strip() for line in last_update_path.read_text(encoding='utf-8').splitlines() if line.strip()]
            if not lines:
                last_update_path.write_text(default_line + '\n', encoding='utf-8')
                return f"Build: {default_line}"

            return f"Build: {lines[-1]}"
        except Exception:
            return "Build: Unknown"
    
    def get_current_prayer(self, prayers_data):
        """Determine which prayer time period we are currently in"""
        now = self.get_current_time()
        is_friday = (self.get_current_date().weekday() == 4)
        _, sunrise_time = self.resolve_sunrise_time(prayers_data)
        shrouq_plus = max(0, int(self.config.get('shrouqplus', 10)))
        shrooq_ends_minutes = max(0, int(getattr(self, 'shrooq_ends_minutes', self.config.get('shrooqends', 15))))
        shrouq_start_time = None
        if sunrise_time:
            shrouq_start_time = (datetime.combine(self.get_current_date(), sunrise_time) + timedelta(minutes=shrouq_plus)).time()

        duhr_athan = self.parse_time(prayers_data.get('DuhrAthan', ''))
        jummah_time = self.jummah_time or self.parse_time('1:30 PM') if is_friday else None
        shrouq_anchor_time = jummah_time if (is_friday and jummah_time) else duhr_athan
        shrouq_end_time = None
        if shrouq_start_time and shrouq_anchor_time:
            shrouq_start_dt = datetime.combine(self.get_current_date(), shrouq_start_time)
            shrouq_anchor_dt = datetime.combine(self.get_current_date(), shrouq_anchor_time)
            shrouq_end_dt = shrouq_anchor_dt - timedelta(minutes=shrooq_ends_minutes)
            if shrouq_end_dt > shrouq_start_dt:
                shrouq_end_time = shrouq_end_dt.time()

        if shrouq_start_time and shrouq_end_time and shrouq_start_time <= now < shrouq_end_time:
            return 'Shrouq'

        if shrouq_end_time and shrouq_anchor_time and shrouq_end_time <= now < shrouq_anchor_time:
            # Intentionally show no current prayer in this gap before Duhr/Jummah.
            return None

        if is_friday:
            asr_athan = self.parse_time(prayers_data.get('AsrAthan', ''))
            friday_duhr_start = self.parse_time('2:15 PM')
            jummah_time = self.jummah_time or self.parse_time('1:30 PM')

            if jummah_time and friday_duhr_start and jummah_time <= now < friday_duhr_start:
                return 'Jummah'

            if friday_duhr_start and asr_athan and friday_duhr_start <= now < asr_athan:
                # Friday: keep midday row unhighlighted after Duhr enters.
                return None

        # Current period boundaries by Athan-style starts, including Shrouq via Sunrise.
        # This keeps prayer highlighting consistent throughout each period.
        prayer_schedule = [
            ('Fajr', self.parse_time(prayers_data.get('FajrAthan', ''))),
            ('Duhr', self.parse_time(prayers_data.get('DuhrAthan', ''))),
            ('Asr', self.parse_time(prayers_data.get('AsrAthan', ''))),
            ('Maghrib', self.parse_time(prayers_data.get('MaghribAthan', ''))),
            ('Isha', self.parse_time(prayers_data.get('IshaAthan', '')))
        ]

        starts = []
        for prayer_name, start_time in prayer_schedule:
            if start_time:
                starts.append((prayer_name, start_time))

        if not starts:
            return None

        # If before first start (Fajr), still in Isha period from previous day
        first_prayer_name, first_start = starts[0]
        if now < first_start:
            return 'Isha'

        # Find period start <= now < next period start
        current_prayer = None
        for i, (prayer_name, start_time) in enumerate(starts):
            if i < len(starts) - 1:
                next_start = starts[i + 1][1]
                if start_time <= now < next_start:
                    current_prayer = prayer_name
                    break
            else:
                # Last prayer period (Isha) continues until next day's Fajr
                if now >= start_time:
                    current_prayer = prayer_name
                    break

        return current_prayer
    
    def get_next_prayer(self, prayers_data):
        """Get the next prayer and its Athan time"""
        current_time = self.get_current_time()  # Use mocked time if in TEST_MODE
        is_friday = (self.get_current_date().weekday() == 4)
        _, sunrise_time = self.resolve_sunrise_time(prayers_data)
        shrouq_plus = max(0, int(self.config.get('shrouqplus', 10)))
        shrouq_start_time = None
        if sunrise_time:
            shrouq_start_time = (datetime.combine(self.get_current_date(), sunrise_time) + timedelta(minutes=shrouq_plus)).time()

        if is_friday:
            jummah_time = self.jummah_time or self.parse_time('1:30 PM')
            asr_athan = self.parse_time(prayers_data.get('AsrAthan', ''))

            if shrouq_start_time and current_time < shrouq_start_time:
                return 'Shrouq', shrouq_start_time

            if shrouq_start_time and jummah_time and shrouq_start_time <= current_time < jummah_time:
                return 'Jummah', jummah_time

            if jummah_time and asr_athan and jummah_time <= current_time < asr_athan:
                return 'Asr', asr_athan

        midday_name = 'Jummah' if is_friday else 'Duhr'

        # Include Shrouq (Sunrise) in the prayer progression
        duhr_athan = self.parse_time(prayers_data.get('DuhrAthan', ''))
        prayer_schedule = [
            ('Fajr', self.parse_time(prayers_data.get('FajrAthan', ''))),
            ('Shrouq', shrouq_start_time),
            (midday_name, duhr_athan),
            ('Asr', self.parse_time(prayers_data.get('AsrAthan', ''))),
            ('Maghrib', self.parse_time(prayers_data.get('MaghribAthan', ''))),
            ('Isha', self.parse_time(prayers_data.get('IshaAthan', '')))
        ]

        # Find next prayer based on current time
        for prayer_name, athan_time in prayer_schedule:
            if athan_time and current_time < athan_time:
                return prayer_name, athan_time

        # If no prayer found, next is Fajr (tomorrow)
        fajr_athan = self.parse_time(prayers_data.get('FajrAthan', ''))
        return 'Fajr', fajr_athan

    def get_next_iqamah_prayer_key(self, prayers_data):
        """Return prayer row key for the next upcoming iqamah (athan-independent)."""
        current_time = self.get_current_time()
        is_friday = (self.get_current_date().weekday() == 4)

        if is_friday:
            schedule = [
                ('Fajr', self.parse_time(prayers_data.get('FajrIqama', ''))),
                ('Jummah', (self.jummah_time or self.parse_time('1:30 PM'))),
                ('Asr', self.parse_time(prayers_data.get('AsrIqama', ''))),
                ('Maghrib', self.parse_time(prayers_data.get('MaghribIqama', ''))),
                ('Isha', self.parse_time(prayers_data.get('IshaIqama', '')))
            ]
        else:
            schedule = [
                ('Fajr', self.parse_time(prayers_data.get('FajrIqama', ''))),
                ('Duhr', self.parse_time(prayers_data.get('DuhrIqama', ''))),
                ('Asr', self.parse_time(prayers_data.get('AsrIqama', ''))),
                ('Maghrib', self.parse_time(prayers_data.get('MaghribIqama', ''))),
                ('Isha', self.parse_time(prayers_data.get('IshaIqama', '')))
            ]

        for prayer_key, iqamah_time in schedule:
            if iqamah_time and current_time < iqamah_time:
                return prayer_key

        return 'Fajr'
    
    def get_countdown(self, target_time):
        """Get countdown text to target time in HH:MM:SS format"""
        if not target_time:
            return '--:--:--'
        
        current_time = self.get_current_time()  # Use mocked time if in TEST_MODE
        mocked_date = self.get_current_date()
        now_dt = datetime.combine(mocked_date, current_time)
        target_dt = datetime.combine(mocked_date, target_time)
        
        # If target is before now, it's tomorrow
        if target_dt < now_dt:
            target_dt = target_dt + timedelta(days=1)
        
        diff = target_dt - now_dt
        total_seconds = int(diff.total_seconds())
        hours, remainder = divmod(total_seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"

    def get_next_line_display_data(self, prayers_data, force_show_arabic=None):
        """Return dynamic label/name/countdown for the prayer-time box.

        During the window between a prayer's Athan and Iqama, show:
        <PRAYER> IQAMAH IN <countdown to iqama>
        Otherwise show:
        NEXT IQAMAH: <PRAYER> IN <countdown to iqamah>
        """
        try:
            now = self.get_current_time()
            is_friday = (self.get_current_date().weekday() == 4)
            current_prayer = self.get_current_prayer(prayers_data)

            if force_show_arabic is None:
                show_arabic = bool(getattr(self, 'salah_names_show_arabic', False))
            else:
                show_arabic = bool(force_show_arabic)
            rtl_mode = show_arabic
            arabic_names = {
                'Fajr': 'الفجر',
                'Duhr': 'الظهر',
                'Dhuhr': 'الظهر',
                'Asr': 'العصر',
                'Maghrib': 'المغرب',
                'Isha': 'العشاء',
                'Jummah': 'الجمعة',
                'Shrouq': 'الشروق'
            }

            def localized_phrase(english_text, arabic_text):
                return arabic_text if show_arabic else english_text

            def localized_prayer_name(prayer_name):
                english_name = (prayer_name or '---').upper()
                arabic_name = arabic_names.get(prayer_name, '---')
                if show_arabic and arabic_name != '---':
                    return arabic_name
                return english_name

            if current_prayer:
                prayer_key = 'Duhr' if current_prayer == 'Jummah' else current_prayer
                current_athan = self.parse_time(prayers_data.get(f'{prayer_key}Athan', ''))
                current_iqamah = self.parse_time(prayers_data.get(f'{prayer_key}Iqama', ''))

                if current_prayer == 'Jummah' and is_friday:
                    current_iqamah = self.jummah_time or self.parse_time('1:30 PM')

                if current_athan and current_iqamah and current_athan <= now < current_iqamah:
                    if prayer_key == 'Duhr' and is_friday:
                        return {
                            'prefix_text': '',
                            'name_text': localized_phrase('Jummah khutbah', 'خطبة الجمعة'),
                            'in_text': localized_phrase(' in ', ' خلال '),
                            'countdown_text': self.get_countdown(current_iqamah),
                            'rtl': rtl_mode
                        }

                    iqamah_name_text = localized_prayer_name(current_prayer)
                    iqamah_countdown_text = self.get_countdown(current_iqamah)

                    return {
                        'prefix_text': localized_phrase('', 'إقامة '),
                        'name_text': iqamah_name_text,
                        'in_text': localized_phrase(' iqamah in ', ' خلال '),
                        'countdown_text': iqamah_countdown_text,
                        'rtl': rtl_mode
                    }

            if is_friday:
                next_iqamah_schedule = [
                    ('Fajr', self.parse_time(prayers_data.get('FajrIqama', ''))),
                    ('Jummah', self.jummah_time or self.parse_time('1:30 PM')),
                    ('Asr', self.parse_time(prayers_data.get('AsrIqama', ''))),
                    ('Maghrib', self.parse_time(prayers_data.get('MaghribIqama', ''))),
                    ('Isha', self.parse_time(prayers_data.get('IshaIqama', ''))),
                ]
            else:
                next_iqamah_schedule = [
                    ('Fajr', self.parse_time(prayers_data.get('FajrIqama', ''))),
                    ('Duhr', self.parse_time(prayers_data.get('DuhrIqama', ''))),
                    ('Asr', self.parse_time(prayers_data.get('AsrIqama', ''))),
                    ('Maghrib', self.parse_time(prayers_data.get('MaghribIqama', ''))),
                    ('Isha', self.parse_time(prayers_data.get('IshaIqama', ''))),
                ]

            next_iqamah_name = None
            next_iqamah_time = None
            for prayer_name, iqamah_time in next_iqamah_schedule:
                if iqamah_time and now < iqamah_time:
                    next_iqamah_name = prayer_name
                    next_iqamah_time = iqamah_time
                    break

            if next_iqamah_name is None:
                next_iqamah_name = 'Fajr'
                next_iqamah_time = self.parse_time(prayers_data.get('FajrIqama', ''))

            self.next_prayer_athan_time = next_iqamah_time
            if is_friday and next_iqamah_name == 'Jummah':
                return {
                    'prefix_text': '',
                    'name_text': localized_phrase('Jummah khutbah', 'خطبة الجمعة'),
                    'in_text': localized_phrase(' in ', ' خلال '),
                    'countdown_text': self.get_countdown(next_iqamah_time),
                    'rtl': rtl_mode
                }
            return {
                'prefix_text': localized_phrase('Next iqamah: ', 'الإقامة القادمة \u200f:\u200f '),
                'name_text': localized_prayer_name(next_iqamah_name),
                'in_text': localized_phrase(' in ', ' خلال '),
                'countdown_text': self.get_countdown(next_iqamah_time),
                'rtl': rtl_mode
            }
        except:
            if force_show_arabic is None:
                show_arabic = bool(getattr(self, 'salah_names_show_arabic', False))
            else:
                show_arabic = bool(force_show_arabic)
            return {
                'prefix_text': 'الإقامة القادمة \u200f:\u200f ' if show_arabic else 'Next iqamah: ',
                'name_text': '---',
                'in_text': ' خلال ' if show_arabic else ' in ',
                'countdown_text': '--:--:--',
                'rtl': show_arabic
            }

    def get_athan_notification_duration_seconds(self):
        """Return athan notification duration in seconds."""
        try:
            duration_value = int(self.config.get('athancalloutduran', 25))
            duration_value = max(0, duration_value)
        except:
            duration_value = 25
        return duration_value

    def _get_athan_overlay_image_path(self):
        """Resolve Muathin background image path for athan overlay."""
        candidates = []

        if getattr(sys, 'frozen', False):
            exe_base = Path(sys.executable).resolve().parent
            candidates.extend([
                exe_base.parent / 'images' / 'Athan' / 'Muathin.png',
                exe_base.parent / 'images' / 'athan' / 'muathin.png',
                exe_base / 'images' / 'Athan' / 'Muathin.png',
                exe_base / 'images' / 'athan' / 'muathin.png',
            ])

            meipass_dir = getattr(sys, '_MEIPASS', None)
            if meipass_dir:
                meipass_path = Path(meipass_dir)
                candidates.extend([
                    meipass_path / 'images' / 'Athan' / 'Muathin.png',
                    meipass_path / 'images' / 'athan' / 'muathin.png',
                ])

        app_base = Path(__file__).resolve().parent
        candidates.extend([
            Path.cwd() / 'images' / 'Athan' / 'Muathin.png',
            Path.cwd() / 'images' / 'athan' / 'muathin.png',
            app_base / 'images' / 'Athan' / 'Muathin.png',
            app_base / 'images' / 'athan' / 'muathin.png',
        ])

        for candidate in candidates:
            try:
                if candidate.is_file():
                    return candidate.resolve()
            except:
                pass
        return None

    def _get_prayer_iqamah_countdown(self, prayer):
        """Return iqamah countdown text for the active athan prayer."""
        try:
            prayers_data = self.get_today_prayers()
            if not prayers_data:
                return '--:--:--'

            prayer_key_map = {
                'fajr': 'Fajr',
                'duhr': 'Duhr',
                'dhuhr': 'Duhr',
                'zuhr': 'Duhr',
                'asr': 'Asr',
                'maghrib': 'Maghrib',
                'isha': 'Isha',
            }
            key = prayer_key_map.get(str(prayer).strip().lower(), str(prayer).strip())
            if key == 'Duhr' and self.get_current_date().weekday() == 4:
                return '--:--:--'
            iqamah_time = self.parse_time(prayers_data.get(f'{key}Iqama', ''))

            now_dt = datetime.combine(self.get_current_date(), self.get_current_time())
            if key == 'Duhr' and now_dt.weekday() == 4 and self.jummah_time:
                iqamah_time = self.jummah_time

            if not iqamah_time:
                return '--:--:--'
            return self.get_countdown(iqamah_time)
        except:
            return '--:--:--'

    def get_athan_blink_state(self, prayers_data):
        """Return active athan prayer during athan window, else (None, False)."""
        try:
            duration_seconds = self.get_athan_notification_duration_seconds()
            if duration_seconds <= 0 or not prayers_data:
                return None, False

            current_date = self.get_current_date()
            now_dt = datetime.combine(current_date, self.get_current_time())
            is_friday = (current_date.weekday() == 4)

            for prayer_name in ['Fajr', 'Duhr', 'Asr', 'Maghrib', 'Isha']:
                if is_friday and prayer_name == 'Duhr':
                    continue
                athan_time = self.parse_time(prayers_data.get(f'{prayer_name}Athan', ''))
                if not athan_time:
                    continue

                athan_dt = datetime.combine(current_date, athan_time)
                elapsed = (now_dt - athan_dt).total_seconds()

                # Active athan window for configured duration from athan time.
                if 0 <= elapsed < duration_seconds:
                    return prayer_name, True
        except:
            pass

        return None, False

    def clear_athan_callout(self):
        """Remove athan callout label if it exists."""
        for item_id in (self.athan_callout_box_id, self.athan_callout_text_id):
            if item_id:
                try:
                    self.canvas.delete(item_id)
                except:
                    pass
        for item_id in getattr(self, '_athan_extra_ids', []):
            try:
                self.canvas.delete(item_id)
            except:
                pass
        self._athan_extra_ids = []
        self.athan_callout_box_id = None
        self.athan_callout_text_id = None
        self.athan_callout_prayer = None
        self._athan_overlay_time_text_id = None
        self._athan_overlay_iqamah_text_id = None
        self._athan_overlay_signature = None

    def _get_athan_box_geometry(self, prayer):
        """Return (x, y, width, height, radius) for a prayer's card box, or None."""
        if prayer in self.prayer_box_fill_styles:
            style = self.prayer_box_fill_styles[prayer]
            return style['x'], style['y'], style['width'], style['height'], style.get('radius', self.us(40, 22))
        if prayer in self.prayer_box_bounds:
            x, y, w, h = self.prayer_box_bounds[prayer]
            return x, y, w, h, self.us(40, 22)
        return None

    def _draw_athan_shine_frame(self, cycle_pos):
        """Draw a blinking right-side athan alert box over the info panels."""
        prayer = self.athan_callout_prayer
        if not prayer:
            return

        width = max(1, self.canvas.winfo_width())
        height = max(1, self.canvas.winfo_height())

        # Keep athan alert continuously visible for the full configured duration.
        blink_visible = True

        prayer_name_map = {
            'fajr': 'Fajr',
            'duhr': 'Dhuhr',
            'dhuhr': 'Dhuhr',
            'zuhr': 'Dhuhr',
            'asr': 'Asr',
            'maghrib': 'Maghrib',
            'isha': 'Isha',
        }
        prayer_display = prayer_name_map.get(str(prayer).strip().lower(), str(prayer).strip().title())
        center_text = f"{prayer_display.upper()} ATHAN NOW"

        title_font = ('Arial', self.fs(52, 28), 'bold')
        time_font = ('Arial', self.fs(90, 44), 'bold')
        right_font = ('Arial', self.fs(38, 20), 'bold')
        current_time_text = self.get_current_time().strftime('%I:%M:%S %p')
        iqamah_countdown_text = self._get_prayer_iqamah_countdown(prayer_display)
        right_line_text = f"{prayer_display.upper()} iqamah in {iqamah_countdown_text}"

        theme_name = self.get_theme_name()
        if theme_name == 'elegent_v2':
            left_panel_x = self.us(36, 18)
            left_panel_y = self.us(236, 150)
            left_panel_w = min(self.us(880, 550), max(self.us(590, 360), width * 0.50))
            right_area_x1 = left_panel_x + left_panel_w + self.us(26, 16)
            right_area_w = max(self.us(320, 200), width - right_area_x1 - self.us(34, 18))
            current_time_y = self.jummah_box_y + self.us(14, 8)
            weather_y_offset = -self.us(10, 6)
            weather_y = self.jummah_box_y + self.jummah_box_h + self.us(12, 8) + weather_y_offset
            weather_bottom = weather_y + self.us(86, 46)

            box_x = right_area_x1
            box_y = left_panel_y
            box_w = right_area_w
            box_h = max((height - box_y) - self.us(10, 6), self.us(480, 300))
        else:
            box_w = min(self.us(620, 360), width * 0.38)
            box_h = min(self.us(520, 300), height * 0.48)
            box_x = width - box_w - self.us(24, 12)
            box_y = self.us(70, 40)

        radius = self.us(40, 22)
        athan_img_path = self._get_athan_overlay_image_path()
        signature = (prayer_display, int(box_x), int(box_y), int(box_w), int(box_h), str(athan_img_path) if athan_img_path else '', 'athan_v5_static_centered_time')
        needs_rebuild = (self._athan_overlay_signature != signature)
        if not needs_rebuild:
            try:
                needs_rebuild = not bool(self.canvas.type(self._athan_overlay_time_text_id))
            except:
                needs_rebuild = True

        if needs_rebuild:
            for item_id in getattr(self, '_athan_extra_ids', []):
                try:
                    self.canvas.delete(item_id)
                except:
                    pass
            self._athan_extra_ids = []
            for attr in ('athan_callout_box_id', 'athan_callout_text_id'):
                iid = getattr(self, attr, None)
                if iid:
                    try:
                        self.canvas.delete(iid)
                    except:
                        pass
                    setattr(self, attr, None)

            if athan_img_path is not None:
                athan_img_path_str = str(athan_img_path)
                if self._athan_overlay_image_path != athan_img_path_str:
                    try:
                        self._athan_overlay_base_image = Image.open(athan_img_path_str).convert('RGBA')
                        self._athan_overlay_image_path = athan_img_path_str
                        self._athan_overlay_image_size = (0, 0)
                        self._athan_overlay_photo = None
                    except Exception as e:
                        self._log(f"Warning: unable to load athan overlay image '{athan_img_path_str}': {e}")
                        self._athan_overlay_base_image = None
                        self._athan_overlay_photo = None
                        self._athan_overlay_image_size = (0, 0)
                        self._athan_overlay_image_path = None

            image_size = (max(1, int(box_w)), max(1, int(box_h)))
            if self._athan_overlay_base_image is not None and (self._athan_overlay_image_size != image_size or self._athan_overlay_photo is None):
                try:
                    inset = max(2, int(self.us(8, 4)))
                    inner_w = max(1, image_size[0] - (inset * 2))
                    inner_h = max(1, image_size[1] - (inset * 2))
                    if hasattr(Image, 'Resampling'):
                        fitted = ImageOps.fit(self._athan_overlay_base_image, (inner_w, inner_h), Image.Resampling.LANCZOS, centering=(0.5, 0.30))
                    else:
                        fitted = ImageOps.fit(self._athan_overlay_base_image, (inner_w, inner_h), Image.LANCZOS, centering=(0.5, 0.30))

                    panel_bg = Image.new('RGBA', image_size, (0, 0, 0, 0))
                    panel_bg.paste(fitted, (inset, inset))

                    clip_radius = max(1, int(radius) - inset)
                    mask = Image.new('L', (inner_w, inner_h), 0)
                    ImageDraw.Draw(mask).rounded_rectangle([(0, 0), (inner_w - 1, inner_h - 1)], radius=clip_radius, fill=255)
                    alpha = panel_bg.split()[3]
                    alpha.paste(mask, (inset, inset))
                    panel_bg.putalpha(alpha)

                    self._athan_overlay_photo = ImageTk.PhotoImage(panel_bg)
                    self._athan_overlay_image_size = image_size
                except Exception as e:
                    self._log(f"Warning: unable to build athan panel image '{self._athan_overlay_image_path}': {e}")
                    self._athan_overlay_photo = None

            if self._athan_overlay_photo is not None:
                bg_id = self.canvas.create_image(box_x, box_y, image=self._athan_overlay_photo, anchor='nw')
            else:
                bg_id = self.draw_rounded_rectangle(
                    box_x,
                    box_y,
                    box_w,
                    box_h,
                    radius,
                    fill='#13233d',
                    outline='',
                    outline_width=0
                )
            self._athan_extra_ids.append(bg_id)

            box_id = self.draw_alpha_fill(
                box_x,
                box_y,
                box_w,
                box_h,
                fill_color='#13233d',
                opacity_percent=0,
                radius=radius,
                outline_color='#efe2b4',
                outline_width=self.us(5, 3)
            )
            self._athan_extra_ids.append(box_id)
            self.athan_callout_box_id = box_id

            title_y = box_y + self.us(72, 38)
            center_id = self.canvas.create_text(
                box_x + (box_w / 2),
                title_y,
                text=center_text,
                font=title_font,
                fill='#0b1f4d',
                anchor='center'
            )
            self._athan_extra_ids.append(center_id)
            self.athan_callout_text_id = center_id

            self._athan_overlay_time_text_id = self.canvas.create_text(
                box_x + (box_w / 2),
                box_y + (box_h * 0.50),
                text=current_time_text,
                font=time_font,
                fill='#0b1f4d',
                anchor='center'
            )
            self._athan_extra_ids.append(self._athan_overlay_time_text_id)

            strip_margin_x = self.us(28, 16)
            strip_h = self.us(108, 60)
            strip_y = box_y + box_h - strip_h - self.us(24, 12)
            strip_id = self.draw_alpha_fill(
                box_x + strip_margin_x,
                strip_y,
                box_w - (strip_margin_x * 2),
                strip_h,
                fill_color='#f4ecd3',
                opacity_percent=88,
                radius=self.us(24, 12),
                outline_color='#c8a95a',
                outline_width=self.us(3, 2)
            )
            self._athan_extra_ids.append(strip_id)

            self._athan_overlay_iqamah_text_id = self.canvas.create_text(
                box_x + (box_w / 2),
                strip_y + (strip_h / 2),
                text=right_line_text,
                font=right_font,
                fill='#0b1f4d',
                anchor='center'
            )
            self._athan_extra_ids.append(self._athan_overlay_iqamah_text_id)

            self._athan_overlay_signature = signature
        else:
            try:
                self.canvas.itemconfig(self.athan_callout_text_id, text=center_text)
            except:
                pass
            try:
                self.canvas.itemconfig(self._athan_overlay_time_text_id, text=current_time_text)
            except:
                pass
            try:
                self.canvas.itemconfig(self._athan_overlay_iqamah_text_id, text=right_line_text)
            except:
                pass

        for item_id in self._athan_extra_ids:
            try:
                self.canvas.tag_raise(item_id)
            except:
                pass

    def schedule_athan_shine_animation(self):
        """Update athan overlay while athan notification window is active."""
        if not getattr(self, '_athan_shine_running', False):
            return
        if not self.athan_callout_prayer:
            self._athan_shine_running = False
            self.clear_athan_callout()
            return
        try:
            elapsed = (datetime.now() - self._athan_shine_cycle_start).total_seconds()
            self._draw_athan_shine_frame(elapsed)
        except Exception as e:
            self._log(f"ERROR in athan shine: {e}")
        try:
            self.root.after(1000, self.schedule_athan_shine_animation)
        except:
            pass

    def _check_athan_shine(self, athan_prayer):
        """Start, continue, or stop the athan shine animation."""
        if not athan_prayer:
            if getattr(self, '_athan_shine_running', False):
                self._athan_shine_running = False
                self.clear_athan_callout()
            return
        # Already running for the same prayer – do nothing (loop keeps going)
        if getattr(self, '_athan_shine_running', False) and self.athan_callout_prayer == athan_prayer:
            return
        # Start (or restart for new prayer)
        self.athan_callout_prayer = athan_prayer
        self._athan_shine_cycle_start = datetime.now()
        self._athan_shine_running = True
        self.schedule_athan_shine_animation()
    
    def schedule_countdown_update(self):
        """Schedule the countdown update to run every second"""
        self.update_countdown()

    def _np_ease(self, t):
        """Smooth cubic ease-in-out."""
        t = max(0.0, min(1.0, t))
        return t * t * (3.0 - 2.0 * t)

    def _np_get_draw_data(self):
        """Return (data_dict_or_None, shift_factor) for current animation frame.

        shift_factor is multiplied by a safe in-panel pixel travel distance in draw code.
        Returns (None, 0.0) when not animating.
        """
        if not self._np_anim_active:
            return None, 0.0
        elapsed = time.monotonic() - self._np_anim_start_mono
        progress = min(1.0, elapsed / max(0.001, self._np_anim_duration))
        if progress < 0.5:
            # Phase 1: old text exits left
            phase = progress / 0.5
            shift_factor = -self._np_ease(phase)  # 0 -> -1
            return self._np_old_data, shift_factor
        else:
            # Phase 2: new text enters from right
            phase = (progress - 0.5) / 0.5
            shift_factor = 1.0 - self._np_ease(phase)  # +1 -> 0
            return self._np_new_data, shift_factor

    def _np_start(self, old_data, new_data):
        """Start next-prayer language slide animation."""
        if self._np_anim_ticker_id is not None:
            try:
                self.root.after_cancel(self._np_anim_ticker_id)
            except:
                pass
            self._np_anim_ticker_id = None
        self._np_old_data = dict(old_data)
        self._np_new_data = dict(new_data)
        self._np_anim_start_mono = time.monotonic()
        self._np_anim_active = True
        self._np_tick()

    def _np_tick(self):
        """Advance next-prayer animation: trigger full redraw each frame."""
        self._np_anim_ticker_id = None
        if not self._np_anim_active:
            return
        elapsed = time.monotonic() - self._np_anim_start_mono
        if elapsed >= self._np_anim_duration:
            self._np_anim_active = False
            self._np_rtl = bool(self._np_new_data.get('rtl', False))
            self.redraw_full_display()
            return
        self.redraw_full_display()
        self._np_anim_ticker_id = self.root.after(40, self._np_tick)

    def _compute_next_prayer_line_layout(self, prefix_text, name_text, in_text, countdown_text, rtl_mode):
        """Measure next-prayer segments and return stable panel/segment positions."""
        segment_gap = self.us(18, 9)
        prefix_width = self.next_prayer_prefix_font.measure(prefix_text)
        name_width = self.next_prayer_line_font.measure(name_text)
        in_width = self.next_prayer_line_font.measure(in_text)
        countdown_width = self.next_prayer_countdown_fixed_width
        total_width = prefix_width + name_width + in_width + countdown_width + (segment_gap * 3)

        left_x = self.next_prayer_line_x - (total_width / 2)
        right_x = self.next_prayer_line_x + (total_width / 2)
        if rtl_mode:
            coords = {
                'prefix': (right_x, 'e'),
                'name': (right_x - prefix_width - segment_gap, 'e'),
                'in': (right_x - prefix_width - segment_gap - name_width - segment_gap, 'e'),
                'countdown': (right_x - prefix_width - segment_gap - name_width - segment_gap - in_width - segment_gap, 'e'),
            }
        else:
            coords = {
                'prefix': (left_x, 'w'),
                'name': (left_x + prefix_width + segment_gap, 'w'),
                'in': (left_x + prefix_width + segment_gap + name_width + segment_gap, 'w'),
                'countdown': (left_x + prefix_width + segment_gap + name_width + segment_gap + in_width + segment_gap, 'w'),
            }

        required_panel_width = max(260, total_width + (self.next_prayer_panel_padding_x * 2))
        if self.next_prayer_max_panel_width:
            required_panel_width = min(required_panel_width, self.next_prayer_max_panel_width)

        return {
            'total_width': total_width,
            'required_panel_width': required_panel_width,
            'coords': coords,
        }

    def update_countdown(self):
        """Update the countdown text every second"""
        _t0 = datetime.now() if ENABLE_PERF_TRACE else None
        try:
            current_date = self.get_current_date()
            if current_date != self._last_seen_date:
                self.handle_date_rollover(current_date)

            periodic_bg_visible = self.should_show_periodic_background_image()
            if periodic_bg_visible != getattr(self, '_background_cycle_visible', False):
                self._background_cycle_visible = periodic_bg_visible
                if not self.iqamah_overlay_visible and not self._is_full_redraw:
                    self.redraw_full_display()

            self.update_salah_name_rotation_state()

            if self.current_time_text_id:
                try:
                    current_time_text = self.get_current_time().strftime('%I:%M:%S %p')
                    self.canvas.itemconfig(self.current_time_text_id, text=current_time_text)
                    for outline_id in self.current_time_outline_ids:
                        self.canvas.itemconfig(outline_id, text=current_time_text)
                except:
                    pass

            if self.next_prayer_prefix_text_id and self.next_prayer_name_text_id and self.next_prayer_in_text_id and self.countdown_text_id:
                try:
                    prayers_data = self.get_today_prayers()
                    current_prayer_now = self.get_current_prayer(prayers_data)

                    # Seed state on first run so we don't trigger unnecessary redraw loops.
                    if self.last_rendered_current_prayer is None:
                        self.last_rendered_current_prayer = current_prayer_now

                    blinking_prayer, blink_visible = self.get_athan_blink_state(prayers_data)

                    if current_prayer_now != self.last_rendered_current_prayer:
                        self.last_rendered_current_prayer = current_prayer_now
                        self.update_prayer_box_highlight_states(current_prayer_now, blinking_prayer, blink_visible)
                    elif not self.iqamah_overlay_visible:
                        self.update_prayer_box_highlight_states(current_prayer_now, blinking_prayer, blink_visible)

                    # Start/stop athan shine animation based on active athan window.
                    if self.iqamah_overlay_visible:
                        self._check_athan_shine(None)
                    else:
                        self._check_athan_shine(blinking_prayer)

                    display_data = self.get_next_line_display_data(prayers_data)
                    prefix_text = display_data['prefix_text']
                    name_text = display_data['name_text']
                    in_text = display_data['in_text']
                    countdown_text = display_data['countdown_text']
                    rtl_mode = bool(display_data.get('rtl', False))

                    if self._np_anim_active:
                        # Keep live countdown current in the animation target
                        if self._np_new_data is not None:
                            self._np_new_data['countdown'] = countdown_text
                    elif rtl_mode != self._np_rtl:
                        # RTL mode changed — build deterministic old/new lines to prevent flash frames.
                        old_display = self.get_next_line_display_data(prayers_data, force_show_arabic=(not rtl_mode))
                        new_display = self.get_next_line_display_data(prayers_data, force_show_arabic=rtl_mode)
                        old_data = {
                            'prefix': old_display.get('prefix_text', ''),
                            'name': old_display.get('name_text', ''),
                            'in_': old_display.get('in_text', ''),
                            'countdown': old_display.get('countdown_text', countdown_text),
                            'rtl': bool(old_display.get('rtl', (not rtl_mode))),
                        }
                        new_data = {
                            'prefix': new_display.get('prefix_text', prefix_text),
                            'name': new_display.get('name_text', name_text),
                            'in_': new_display.get('in_text', in_text),
                            'countdown': new_display.get('countdown_text', countdown_text),
                            'rtl': bool(new_display.get('rtl', rtl_mode)),
                        }
                        self._np_start(old_data, new_data)
                    else:
                        # Same language — just update the live countdown text directly
                        self._np_rtl = rtl_mode
                        try:
                            self.canvas.itemconfig(self.countdown_text_id, text=countdown_text)
                        except:
                            pass
                except:
                    pass
        except Exception as e:
            self._log(f"ERROR in update_countdown: {e}")
        
        # Schedule next update in 1000ms (1 second)
        try:
            self.root.after(1000, self.update_countdown)
        except:
            pass

        if ENABLE_PERF_TRACE and _t0 is not None:
            elapsed_ms = (datetime.now() - _t0).total_seconds() * 1000
            if elapsed_ms > 120:
                last_ts = self._perf_last_log.get('update_countdown', 0)
                now_ts = datetime.now().timestamp()
                if now_ts - last_ts >= 2:
                    self._perf_last_log['update_countdown'] = now_ts
                    self._log(f"[PERF] update_countdown slow: {elapsed_ms:.1f}ms")
    
    def schedule_iqamah_countdown_check(self):
        """Schedule the Iqamah countdown overlay check to run every second"""
        self.check_iqamah_countdown()
    
    def check_iqamah_countdown(self):
        """Check and manage iqamah overlay phases: pre-countdown and 3-minute post phase."""
        _t0 = datetime.now() if ENABLE_PERF_TRACE else None
        try:
            current_time = self.get_current_time()
            prayers_data = self.get_today_prayers()
            
            if not prayers_data:
                self.root.after(1000, self.check_iqamah_countdown)
                return
            
            # Determine active overlay prayer from Athan->Iqama windows only
            # (Shrouq has no iqamah overlay and is intentionally excluded here).
            is_friday = (self.get_current_date().weekday() == 4)
            overlay_prayers = ['Fajr', 'Duhr', 'Asr', 'Maghrib', 'Isha']
            pre_countdown_prayer = None
            post_iqamah_prayer = None
            post_iqamah_time = None

            mocked_date = self.get_current_date()
            now_dt = datetime.combine(mocked_date, current_time)
            friday_duhr_start = self.parse_time('2:15 PM') if is_friday else None
            khutbah_overlay_end_time = self.parse_time(self.config.get('khutbahoverlayendsat', '2:00 PM')) if is_friday else None

            # After post-iqamah phase ends, keep app on main page for a short cooldown
            if self.iqamah_overlay_cooldown_until and now_dt < self.iqamah_overlay_cooldown_until:
                if self.iqamah_overlay_visible:
                    self.hide_iqamah_overlay()
                self.root.after(1000, self.check_iqamah_countdown)
                return

            for prayer in overlay_prayers:
                # Friday rule: keep Jummah khutbah countdown, but skip Duhr iqamah phase after Duhr start.
                if (
                    prayer == 'Duhr'
                    and is_friday
                    and friday_duhr_start
                    and now_dt >= datetime.combine(mocked_date, friday_duhr_start)
                ):
                    continue

                display_prayer = 'Jummah' if (prayer == 'Duhr' and is_friday) else prayer

                athan_time = self.parse_time(prayers_data.get(f'{prayer}Athan', ''))
                iqamah_time = self.parse_time(prayers_data.get(f'{prayer}Iqama', ''))
                if prayer == 'Duhr' and is_friday:
                    iqamah_time = self.jummah_time or self.parse_time('1:30 PM')

                if not athan_time or not iqamah_time:
                    continue

                athan_dt = datetime.combine(mocked_date, athan_time)
                iqamah_dt = datetime.combine(mocked_date, iqamah_time)
                post_end_dt = iqamah_dt + timedelta(seconds=self.iqamah_post_duration_seconds)

                # Friday khutbah countdown lead time is configurable (default: 2 minutes).
                try:
                    friday_khutbah_minutes = int(self.config.get('fridaykhutbahcountdown', 2))
                except:
                    friday_khutbah_minutes = 2
                friday_khutbah_minutes = max(1, friday_khutbah_minutes)
                friday_window_seconds = friday_khutbah_minutes * 60

                if prayer == 'Duhr' and is_friday:
                    time_until_jummah = (iqamah_dt - now_dt).total_seconds()
                    if 0 < time_until_jummah <= friday_window_seconds:
                        pre_countdown_prayer = display_prayer
                        self.current_prayer_iqamah_time = iqamah_time
                        break

                if athan_dt <= now_dt < iqamah_dt:
                    pre_countdown_prayer = display_prayer
                    self.current_prayer_iqamah_time = iqamah_time
                    break

                if iqamah_dt <= now_dt < post_end_dt and post_iqamah_prayer is None:
                    post_iqamah_prayer = display_prayer
                    post_iqamah_time = iqamah_time

            if is_friday:
                jummah_start_time = self.jummah_time or self.parse_time('1:30 PM')
                if jummah_start_time and khutbah_overlay_end_time:
                    jummah_start_dt = datetime.combine(mocked_date, jummah_start_time)
                    khutbah_end_dt = datetime.combine(mocked_date, khutbah_overlay_end_time)
                    if jummah_start_dt <= now_dt < khutbah_end_dt:
                        self.current_prayer_name = 'Jummah'
                        self.current_prayer_iqamah_time = jummah_start_time
                        if (not self.iqamah_overlay_visible) or self.iqamah_overlay_mode != 'khutbah':
                            self.iqamah_overlay_ids = []
                            self.show_khutbah_overlay()
                        else:
                            self.update_iqamah_overlay_countdown()
                        self.root.after(1000, self.check_iqamah_countdown)
                        return

            if pre_countdown_prayer:
                self.current_prayer_name = pre_countdown_prayer
                iqamah_dt = datetime.combine(mocked_date, self.current_prayer_iqamah_time)
                time_diff = (iqamah_dt - now_dt).total_seconds()

                # Show countdown overlay window:
                # - Friday Jummah khutbah uses configurable lead minutes
                # - Other prayers use the existing 2-minute window
                overlay_window_seconds = friday_window_seconds if (is_friday and self.current_prayer_name == 'Jummah') else 120
                if 0 < time_diff <= overlay_window_seconds:
                    if (not self.iqamah_overlay_visible
                        or self.iqamah_overlay_mode != 'countdown'):
                        self.iqamah_overlay_ids = []
                        self.show_iqamah_overlay()
                    else:
                        self.update_iqamah_overlay_countdown()
                else:
                    if self.iqamah_overlay_visible:
                        self.hide_iqamah_overlay()
            elif post_iqamah_prayer:
                # Skip post-iqamah overlay for Friday Jummah
                is_friday_jummah = (post_iqamah_prayer == 'Jummah' and is_friday)
                if not is_friday_jummah:
                    self.current_prayer_name = post_iqamah_prayer
                    self.current_prayer_iqamah_time = post_iqamah_time

                    if (not self.iqamah_overlay_visible
                        or self.iqamah_overlay_mode != 'post'):
                        self.iqamah_overlay_ids = []
                        self.show_post_iqamah_overlay()
                    else:
                        self.update_iqamah_overlay_countdown()
                else:
                    # For Friday Jummah, just hide overlay if visible
                    if self.iqamah_overlay_visible:
                        self.hide_iqamah_overlay()
            else:
                if self.iqamah_overlay_visible:
                    self.hide_iqamah_overlay()
        
        except Exception as e:
            self._log(f"ERROR in check_iqamah_countdown: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()
        
        # Schedule next check in 1000ms (1 second)
        try:
            self.root.after(1000, self.check_iqamah_countdown)
        except:
            pass

        if ENABLE_PERF_TRACE and _t0 is not None:
            elapsed_ms = (datetime.now() - _t0).total_seconds() * 1000
            if elapsed_ms > 120:
                last_ts = self._perf_last_log.get('check_iqamah_countdown', 0)
                now_ts = datetime.now().timestamp()
                if now_ts - last_ts >= 2:
                    self._perf_last_log['check_iqamah_countdown'] = now_ts
                    self._log(f"[PERF] check_iqamah_countdown slow: {elapsed_ms:.1f}ms")
    
    def show_iqamah_overlay(self):
        """Show the full-screen Iqamah countdown overlay"""
        try:
            # Keep day-before prayer-change ribbon hidden while overlay is active.
            try:
                self.canvas.itemconfig('prayer_change_ribbon', state='hidden')
            except:
                pass

            # Cancel any existing toggle timer before redrawing
            toggle_id = getattr(self, '_iqamah_countdown_toggle_id', None)
            if toggle_id:
                self.root.after_cancel(toggle_id)
                self._iqamah_countdown_toggle_id = None

            width = self.canvas.winfo_width()
            height = self.canvas.winfo_height()
            
            # Keep configured background visible and add a soft white veil for readability.
            overlay_bg = self.draw_overlay_background(width, height, tags='iqamah_overlay')
            self.iqamah_overlay_ids.append(overlay_bg)

            readability_veil = self.draw_alpha_fill(
                0, 0, width, height,
                fill_color='white',
                opacity_percent=self.overlay_opacity_percent,
                radius=0,
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(readability_veil)

            self.draw_background_image_label(width, height, tags='iqamah_overlay')

            # Live current time (bottom-left, white rounded background)
            current_time_text = self.get_current_time().strftime('%I:%M:%S %p')
            time_font = ('Arial', self.fs(50, 24), 'bold')
            time_pad_x = self.us(20, 10)
            time_pad_y = self.us(10, 5)
            time_radius = self.us(20, 10)
            import tkinter.font as _tf
            _tw = _tf.Font(font=time_font).measure(current_time_text)
            _th = _tf.Font(font=time_font).metrics('linespace')
            time_bg_x = self.us(20, 10)
            time_bg_y = height - self.us(20, 10) - _th - time_pad_y * 2
            time_bg_id = self.draw_rounded_rectangle(
                time_bg_x, time_bg_y,
                _tw + time_pad_x * 2, _th + time_pad_y * 2,
                time_radius,
                fill='white', outline='#cccccc', outline_width=1,
                tags=('iqamah_overlay', 'iqamah_overlay_time_bg')
            )
            self.iqamah_overlay_ids.append(time_bg_id)
            top_left_time = self.canvas.create_text(
                time_bg_x + time_pad_x, time_bg_y + time_pad_y,
                text=current_time_text,
                font=time_font,
                fill='#1a3a5f',
                anchor='nw',
                tags=('iqamah_overlay', 'iqamah_overlay_current_time')
            )
            self.iqamah_overlay_ids.append(top_left_time)

            line1_y = height * 0.10
            countdown_y = line1_y + self.us(145, 80)
            change_notice_y = countdown_y + self.us(175, 95)
            notice_y = change_notice_y + self.us(90, 50)
            icon_y = notice_y + self.us(200, 112)
            icon_x = width / 2
            is_friday_khutbah = (self.current_prayer_name == 'Jummah' and self.get_current_date().weekday() == 4)
            friday_hadith_text = ''
            friday_hadith_text_en = ''
            prayer_line_text = f"{self.current_prayer_name.upper()} iqamah in"
            instruction_line_text = 'Please put your cell phone on silent mode'
            instruction_font_size = self.fs(68, 32)
            iqamah_change_notice = self.get_iqamah_change_notice_text()

            if is_friday_khutbah:
                prayer_line_text = 'Jummah khutbah in'
                instruction_line_text = 'Talking is forbidden during Khutbahs'
                instruction_font_size = self.fs(74, 34)
                friday_hadith_text = 'عن أنس رضي الله عنه أن الرسول صلى الله عليه وسلم قال: إذا قلت لصاحبك أنصت والإمام يخطب يوم الجمعة فقد لغوت'
                friday_hadith_text_en = "Anas (RA) reported that the Messenger of Allah (PBUH) said: If you tell your companion 'Be quiet' while the Imam is delivering the Friday khutbah, you have spoken in vain."
                icon_y = icon_y - self.us(26, 14)

            # Prayer line: PRAYERNAME IQAMAH IN (green with white outline)
            prayer_text = self.draw_outlined_text(
                width / 2, line1_y,
                text=prayer_line_text,
                font=('Arial', self.fs(78, 34), 'bold'),
                fill='#2E7D32',
                outline='white',
                outline_px=self.us(3, 2),
                tags=('iqamah_overlay', 'iqamah_prayer_line_text')
            )
            self.iqamah_overlay_ids.append(prayer_text)

            # Countdown time (will be updated every second)
            countdown = self.get_iqamah_countdown()
            countdown_text = self.draw_outlined_text(
                width / 2, countdown_y,
                text=countdown,
                font=('Arial', self.fs(170, 72), 'bold'),
                fill='#d32f2f',
                outline='white',
                outline_px=self.us(4, 2),
                tags=('iqamah_overlay', 'iqamah_countdown_time')
            )
            self.iqamah_overlay_ids.append(countdown_text)

            # Iqamah change notice (between countdown and phone notice)
            if iqamah_change_notice:
                prayer_display = self.current_prayer_name or ''
                left_text = f'{prayer_display} iqamah changes to '
                right_text = f'{iqamah_change_notice} TOMORROW'
                notice_font_size = self.fs(78, 36)
                min_notice_font_size = self.fs(50, 24)
                max_notice_text_width = width - self.us(120, 60)
                while notice_font_size > min_notice_font_size:
                    test_font = ('Arial', notice_font_size, 'bold')
                    if tkfont.Font(font=test_font).measure(left_text + right_text) <= max_notice_text_width:
                        break
                    notice_font_size -= 1
                notice_font = ('Arial', notice_font_size, 'bold')
                outline_px = self.us(3, 2)

                change_notice_left = self.draw_outlined_text(
                    width / 2, change_notice_y,
                    text=left_text + right_text,
                    font=notice_font,
                    fill='#2E7D32',
                    outline='white',
                    outline_px=outline_px,
                    tags=('iqamah_overlay', 'iqamah_overlay_change_notice')
                )
                self.iqamah_overlay_ids.append(change_notice_left)

                # Overlay the right portion in red on top
                left_width = tkfont.Font(font=notice_font).measure(left_text)
                right_width = tkfont.Font(font=notice_font).measure(right_text)
                total_width = left_width + right_width
                right_x = (width / 2) + (total_width / 2) - right_width

                change_notice_right = self.draw_outlined_text(
                    right_x + right_width / 2, change_notice_y,
                    text=right_text,
                    font=notice_font,
                    fill='#d32f2f',
                    outline='white',
                    outline_px=outline_px,
                    tags=('iqamah_overlay', 'iqamah_overlay_change_notice')
                )
                self.iqamah_overlay_ids.append(change_notice_right)

            # Cell phone notice (black and bigger)
            instruction_x = width / 2
            instruction_y = notice_y
            instruction_anchor = 'center'
            instruction_font = ('Arial', instruction_font_size, 'bold')
            if is_friday_khutbah:
                # Friday: pin warning in its own wide white box from time box edge to near screen edge.
                warning_left = time_bg_x + (_tw + time_pad_x * 2) + self.us(18, 10)
                warning_right = width - self.us(20, 10)
                warning_y = time_bg_y
                warning_h = _th + time_pad_y * 2
                if warning_right > warning_left + self.us(180, 90):
                    warning_text = instruction_line_text
                    try:
                        change_every_seconds = int(self.config.get('arabicchangeevery', 30))
                        change_every_seconds = max(1, change_every_seconds)
                    except:
                        change_every_seconds = 30
                    try:
                        arabic_duration_seconds = int(self.config.get('arabicnameduration', 10))
                        arabic_duration_seconds = max(0, arabic_duration_seconds)
                    except:
                        arabic_duration_seconds = 5
                    arabic_duration_seconds = min(arabic_duration_seconds, change_every_seconds)
                    now_dt = datetime.combine(self.get_current_date(), self.get_current_time())
                    seconds_into_cycle = int(now_dt.timestamp()) % change_every_seconds
                    if arabic_duration_seconds > 0 and seconds_into_cycle < arabic_duration_seconds:
                        warning_text = 'الكلام محرم اثناء الخطبتين'

                    warning_bg_id = self.draw_rounded_rectangle(
                        warning_left,
                        warning_y,
                        warning_right - warning_left,
                        warning_h,
                        self.us(20, 10),
                        fill='white', outline='#cccccc', outline_width=1,
                        tags=('iqamah_overlay', 'iqamah_friday_warning_bg')
                    )
                    self.iqamah_overlay_ids.append(warning_bg_id)

                    friday_warning_id = self.canvas.create_text(
                        (warning_left + warning_right) / 2,
                        warning_y + (warning_h / 2),
                        text=warning_text,
                        font=('Arial', self.fs(42, 20), 'bold'),
                        fill='black',
                        anchor='center',
                        tags=('iqamah_overlay', 'iqamah_friday_warning_text')
                    )
                    self.iqamah_overlay_ids.append(friday_warning_id)

                    # Move no-phone icon to the right, above the Friday warning box.
                    icon_x = warning_right - self.us(120, 62)
                    icon_y = warning_y - self.us(94, 50)
            else:
                instruction_text = self.canvas.create_text(
                    instruction_x, instruction_y,
                    text=instruction_line_text,
                    font=instruction_font,
                    fill='black',
                    anchor=instruction_anchor,
                    tags=('iqamah_overlay', 'iqamah_instruction_text')
                )
                self.iqamah_overlay_ids.append(instruction_text)

            if is_friday_khutbah and friday_hadith_text:
                # Keep both languages visible together: Arabic on top, English translation below.
                hadith_text = f'{friday_hadith_text}\n{friday_hadith_text_en}'
                hadith_center_y = countdown_y + self.us(348, 178)
                hadith_text_id = self.draw_outlined_text(
                    width / 2,
                    hadith_center_y,
                    text=hadith_text,
                    font=('Arial', self.fs(54, 26), 'bold'),
                    fill='black',
                    outline='white',
                    outline_px=self.us(3, 2),
                    width=self.us(1750, 920),
                    justify='center',
                    anchor='center',
                    tags=('iqamah_overlay', 'iqamah_khutbah_hadith_text')
                )
                self.iqamah_overlay_ids.append(hadith_text_id)

                # Keep brackets around the Arabic line only.
                hadith_bbox = self.canvas.bbox(hadith_text_id)
                if hadith_bbox:
                    _bx1, by1, _bx2, by2 = hadith_bbox
                    arabic_line_height = max(1, tkfont.Font(font=('Arial', self.fs(54, 26), 'bold')).metrics('linespace'))
                    first_line_y = by1 + (arabic_line_height / 2)
                    second_line_y = min(by2 - (arabic_line_height / 2), first_line_y + arabic_line_height)
                    arabic_font = ('Arial', self.fs(54, 26), 'bold')
                    arabic_width = tkfont.Font(font=arabic_font).measure(friday_hadith_text)
                    arabic_width = min(arabic_width, self.us(1750, 920))
                    arabic_center_x = width / 2

                    bracket_gap = self.us(1, 0)
                    bracket_font = ('Arial', self.fs(62, 28), 'bold')

                    right_bracket_id = self.draw_outlined_text(
                        arabic_center_x + (arabic_width / 2) + bracket_gap,
                        first_line_y,
                        text='﴿',
                        font=bracket_font,
                        fill='black',
                        outline='white',
                        outline_px=self.us(3, 2),
                        anchor='w',
                        tags=('iqamah_overlay', 'iqamah_khutbah_hadith_text')
                    )
                    self.iqamah_overlay_ids.append(right_bracket_id)

                    left_bracket_id = self.draw_outlined_text(
                        arabic_center_x - (arabic_width / 2) - bracket_gap,
                        second_line_y,
                        text='﴾',
                        font=bracket_font,
                        fill='black',
                        outline='white',
                        outline_px=self.us(3, 2),
                        anchor='e',
                        tags=('iqamah_overlay', 'iqamah_khutbah_hadith_text')
                    )
                    self.iqamah_overlay_ids.append(left_bracket_id)

            # Larger centered no-phone icon beneath the notice
            icon_ids = self.draw_no_phone_icon(icon_x, icon_y, size=self.us(240, 130), tags='iqamah_overlay')
            
            # Raise overlay to top of canvas stacking order
            self.canvas.tag_raise('iqamah_overlay')
            
            self.iqamah_overlay_visible = True
            self.iqamah_overlay_mode = 'countdown'

            # Start English/Arabic text toggle for countdown overlay
            self._iqamah_countdown_lang_english = True
            self._iqamah_countdown_is_friday = is_friday_khutbah
            self._iqamah_countdown_prayer_name = self.current_prayer_name
            try:
                change_every_seconds = int(self.config.get('arabicchangeevery', 30))
                change_every_seconds = max(1, change_every_seconds)
            except:
                change_every_seconds = 30
            try:
                arabic_duration_seconds = int(self.config.get('arabicnameduration', 10))
                arabic_duration_seconds = max(0, arabic_duration_seconds)
            except:
                arabic_duration_seconds = 5
            arabic_duration_seconds = min(arabic_duration_seconds, change_every_seconds)
            english_duration_seconds = max(1, change_every_seconds - arabic_duration_seconds)
            self._iqamah_countdown_toggle_id = self.root.after(english_duration_seconds * 1000, self._schedule_iqamah_countdown_text_toggle)

        except Exception as e:
            self._log(f"ERROR in show_iqamah_overlay: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()

    def show_post_iqamah_overlay(self):
        """Show post-iqamah overlay for 3 minutes with ayah and prayer notice."""
        try:
            # Keep day-before prayer-change ribbon hidden while overlay is active.
            try:
                self.canvas.itemconfig('prayer_change_ribbon', state='hidden')
            except:
                pass

            # Cancel any existing toggle timer before redrawing
            toggle_id = getattr(self, '_post_overlay_toggle_id', None)
            if toggle_id:
                self.root.after_cancel(toggle_id)
                self._post_overlay_toggle_id = None

            self.clear_iqamah_overlay_items()
            width = self.canvas.winfo_width()
            height = self.canvas.winfo_height()

            overlay_bg = self.draw_overlay_background(width, height, tags='iqamah_overlay')
            self.iqamah_overlay_ids.append(overlay_bg)

            # Add a soft white veil so text remains readable while background stays visible.
            readability_veil = self.draw_alpha_fill(
                0, 0, width, height,
                fill_color='white',
                opacity_percent=self.overlay_opacity_percent,
                radius=0,
                tags='iqamah_overlay'
            )

            self.iqamah_overlay_ids.append(readability_veil)

            self.draw_background_image_label(width, height, tags='iqamah_overlay')

            # Live current time (bottom-left, white rounded background)
            current_time_text = self.get_current_time().strftime('%I:%M:%S %p')
            time_font = ('Arial', self.fs(50, 24), 'bold')
            time_pad_x = self.us(20, 10)
            time_pad_y = self.us(10, 5)
            time_radius = self.us(20, 10)
            import tkinter.font as _tf
            _tw = _tf.Font(font=time_font).measure(current_time_text)
            _th = _tf.Font(font=time_font).metrics('linespace')
            time_bg_x = self.us(20, 10)
            time_bg_y = height - self.us(20, 10) - _th - time_pad_y * 2
            time_bg_id = self.draw_rounded_rectangle(
                time_bg_x, time_bg_y,
                _tw + time_pad_x * 2, _th + time_pad_y * 2,
                time_radius,
                fill='white', outline='#cccccc', outline_width=1,
                tags=('iqamah_overlay', 'iqamah_overlay_time_bg')
            )
            self.iqamah_overlay_ids.append(time_bg_id)
            top_left_time = self.canvas.create_text(
                time_bg_x + time_pad_x, time_bg_y + time_pad_y,
                text=current_time_text,
                font=time_font,
                fill='#1a3a5f',
                anchor='nw',
                tags=('iqamah_overlay', 'iqamah_overlay_current_time')
            )
            self.iqamah_overlay_ids.append(top_left_time)

            # Pull the main post-prayer stack slightly upward and place
            # "Prayer is now" below the phone icon (above masjid name area).
            stack_shift_up = self.us(78, 40)
            ayah_y = (height * 0.24) - stack_shift_up
            notice_y = ayah_y + self.us(175, 98)
            icon_y = notice_y + self.us(205, 116)
            prayer_now_y = icon_y + self.us(205, 112)

            ayah_text = self.draw_outlined_text(
                width / 2, ayah_y,
                text='﴾ إِنَّ الصَّلَاةَ كَانَتْ عَلَى الْمُؤْمِنِينَ كِتَابًا مَوْقُوتًا ﴿',
                font=('Arial', self.fs(74, 36), 'bold'),
                fill='#2E7D32',
                outline='white',
                outline_px=self.us(3, 2),
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(ayah_text)

            instruction_text = self.canvas.create_text(
                width / 2, notice_y,
                text='Please put your cell phone on silent mode',
                font=('Arial', self.fs(62, 30), 'bold'),
                fill='black',
                tags=('iqamah_overlay', 'post_instruction_text')
            )
            self.iqamah_overlay_ids.append(instruction_text)

            icon_ids = self.draw_no_phone_icon(width / 2, icon_y, size=self.us(240, 130), tags='iqamah_overlay')
            self.iqamah_overlay_ids.extend(icon_ids)

            prayer_now_text = self.draw_outlined_text(
                width / 2, prayer_now_y,
                text='Prayer is now',
                font=('Arial', self.fs(92, 42), 'bold'),
                fill='#d32f2f',
                outline='white',
                outline_px=self.us(3, 2),
                tags=('iqamah_overlay', 'post_prayer_now_text')
            )
            self.iqamah_overlay_ids.append(prayer_now_text)

            # Raise overlay to top of canvas stacking order
            self.canvas.tag_raise('iqamah_overlay')

            self.iqamah_overlay_visible = True
            self.iqamah_overlay_mode = 'post'

            # Start English/Arabic text toggle (English 10s, Arabic 5s)
            self._post_overlay_lang_english = True
            self._post_overlay_toggle_id = self.root.after(10000, self._schedule_post_overlay_text_toggle)

        except Exception as e:
            self._log(f"ERROR in show_post_iqamah_overlay: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()

    def show_khutbah_overlay(self):
        """Show Friday khutbah-in-progress overlay from Jummah start until configured end time."""
        try:
            try:
                self.canvas.itemconfig('prayer_change_ribbon', state='hidden')
            except:
                pass

            self.clear_iqamah_overlay_items()
            width = self.canvas.winfo_width()
            height = self.canvas.winfo_height()

            overlay_bg = self.canvas.create_rectangle(
                0, 0, width, height,
                fill='#f7f5ef',
                outline=''
                ,tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(overlay_bg)

            current_time_text = self.get_current_time().strftime('%I:%M:%S %p')
            time_font = ('Arial', self.fs(50, 24), 'bold')
            time_pad_x = self.us(20, 10)
            time_pad_y = self.us(10, 5)
            time_radius = self.us(20, 10)
            import tkinter.font as _tf
            _tw = _tf.Font(font=time_font).measure(current_time_text)
            _th = _tf.Font(font=time_font).metrics('linespace')
            time_bg_x = self.us(20, 10)
            time_bg_y = height - self.us(20, 10) - _th - time_pad_y * 2
            time_bg_id = self.draw_rounded_rectangle(
                time_bg_x, time_bg_y,
                _tw + time_pad_x * 2, _th + time_pad_y * 2,
                time_radius,
                fill='white', outline='#cccccc', outline_width=1,
                tags=('iqamah_overlay', 'iqamah_overlay_time_bg')
            )
            self.iqamah_overlay_ids.append(time_bg_id)
            top_left_time = self.canvas.create_text(
                time_bg_x + time_pad_x, time_bg_y + time_pad_y,
                text=current_time_text,
                font=time_font,
                fill='#1a3a5f',
                anchor='nw',
                tags=('iqamah_overlay', 'iqamah_overlay_current_time')
            )
            self.iqamah_overlay_ids.append(top_left_time)

            heading_y = height * 0.22
            arabic_heading_y = heading_y + self.us(142, 78)
            warning_y = arabic_heading_y + self.us(150, 82)
            arabic_warning_y = warning_y + self.us(92, 48)
            icon_y = arabic_warning_y + self.us(190, 104)

            heading_id = self.draw_outlined_text(
                width / 2, heading_y,
                text='Khutbah is in progress',
                font=('Arial', self.fs(96, 44), 'bold'),
                fill='#d32f2f',
                outline='white',
                outline_px=self.us(3, 2),
                tags=('iqamah_overlay', 'khutbah_progress_heading')
            )
            self.iqamah_overlay_ids.append(heading_id)

            arabic_heading_id = self.draw_outlined_text(
                width / 2, arabic_heading_y,
                text='الخطبة جارية الآن',
                font=('Arial', self.fs(86, 40), 'bold'),
                fill='#2E7D32',
                outline='white',
                outline_px=self.us(3, 2),
                tags=('iqamah_overlay', 'khutbah_progress_heading_ar')
            )
            self.iqamah_overlay_ids.append(arabic_heading_id)

            warning_id = self.canvas.create_text(
                width / 2, warning_y,
                text='Talking is forbidden',
                font=('Arial', self.fs(72, 34), 'bold'),
                fill='black',
                anchor='center',
                tags=('iqamah_overlay', 'khutbah_warning_text')
            )
            self.iqamah_overlay_ids.append(warning_id)

            arabic_warning_id = self.canvas.create_text(
                width / 2, arabic_warning_y,
                text='الكلام محرم اثناء الخطبتين',
                font=('Arial', self.fs(66, 32), 'bold'),
                fill='black',
                anchor='center',
                tags=('iqamah_overlay', 'khutbah_warning_text_ar')
            )
            self.iqamah_overlay_ids.append(arabic_warning_id)

            icon_ids = self.draw_no_phone_icon(width / 2, icon_y, size=self.us(240, 130), tags='iqamah_overlay')
            self.iqamah_overlay_ids.extend(icon_ids)

            self.canvas.tag_raise('iqamah_overlay')
            self.iqamah_overlay_visible = True
            self.iqamah_overlay_mode = 'khutbah'
        except Exception as e:
            self._log(f"ERROR in show_khutbah_overlay: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()

    def _schedule_iqamah_countdown_text_toggle(self):
        """Toggle instruction & prayer-line text on countdown overlay between English and Arabic every 5s."""
        if not self.iqamah_overlay_visible or self.iqamah_overlay_mode != 'countdown':
            self._iqamah_countdown_toggle_id = None
            return

        try:
            change_every_seconds = int(self.config.get('arabicchangeevery', 30))
            change_every_seconds = max(1, change_every_seconds)
        except:
            change_every_seconds = 30
        try:
            arabic_duration_seconds = int(self.config.get('arabicnameduration', 10))
            arabic_duration_seconds = max(0, arabic_duration_seconds)
        except:
            arabic_duration_seconds = 5
        arabic_duration_seconds = min(arabic_duration_seconds, change_every_seconds)
        english_duration_seconds = max(1, change_every_seconds - arabic_duration_seconds)

        if arabic_duration_seconds <= 0:
            # Setting disables Arabic phase; keep English and re-check cadence.
            self._iqamah_countdown_lang_english = True
            self._iqamah_countdown_toggle_id = self.root.after(change_every_seconds * 1000, self._schedule_iqamah_countdown_text_toggle)
            return

        arabic_names = {
            'Fajr': 'الفجر', 'Duhr': 'الظهر', 'Dhuhr': 'الظهر',
            'Asr': 'العصر', 'Maghrib': 'المغرب', 'Isha': 'العشاء',
            'Jummah': 'الجمعة', 'Shrouq': 'الشروق'
        }
        self._iqamah_countdown_lang_english = not self._iqamah_countdown_lang_english
        is_friday = getattr(self, '_iqamah_countdown_is_friday', False)
        prayer_name = getattr(self, '_iqamah_countdown_prayer_name', '') or ''
        if self._iqamah_countdown_lang_english:
            if is_friday:
                prayer_line = 'Jummah khutbah in'
                instr = 'Talking is forbidden during Khutbahs'
            else:
                prayer_line = f"{prayer_name.upper()} iqamah in"
                instr = 'Please put your cell phone on silent mode'
        else:
            arabic_name = arabic_names.get(prayer_name, prayer_name)
            if is_friday:
                prayer_line = f'خطبة {arabic_name} بعد'
                instr = 'الكلام محرم اثناء الخطبتين'
            else:
                prayer_line = f'إقامة {arabic_name} بعد'
                instr = 'يرجى وضع هاتفك على الوضع الصامت'
        self._start_iqamah_countdown_text_transition(prayer_line, instr)

        # Friday warning is rendered in its own box, so update it directly.
        if is_friday:
            for item_id in self.canvas.find_withtag('iqamah_friday_warning_text'):
                try:
                    self.canvas.itemconfig(item_id, text=instr)
                except:
                    pass

        delay_seconds = english_duration_seconds if self._iqamah_countdown_lang_english else arabic_duration_seconds
        self._iqamah_countdown_toggle_id = self.root.after(delay_seconds * 1000, self._schedule_iqamah_countdown_text_toggle)

    def _clear_iqamah_countdown_text_transition_artifacts(self):
        """Cancel in-progress iqamah countdown text transition and clear temporary items."""
        transition_after_id = getattr(self, '_iqamah_countdown_text_transition_after_id', None)
        if transition_after_id is not None:
            try:
                self.root.after_cancel(transition_after_id)
            except:
                pass
            self._iqamah_countdown_text_transition_after_id = None

        # Remove all temporary transition layers (including outline copies).
        try:
            self.canvas.delete('iqamah_countdown_lang_transition')
        except:
            pass

        for item_id in getattr(self, '_iqamah_countdown_text_transition_temp_ids', []):
            try:
                self.canvas.delete(item_id)
            except:
                pass
        self._iqamah_countdown_text_transition_temp_ids = []
        self._iqamah_countdown_text_transition_payload = None

    def _start_iqamah_countdown_text_transition(self, next_prayer_line, next_instruction_line):
        """Animate countdown overlay text between English and Arabic using slide/fade."""
        if not self.iqamah_overlay_visible or self.iqamah_overlay_mode != 'countdown':
            return

        prayer_ids = list(self.canvas.find_withtag('iqamah_prayer_line_text'))
        instruction_ids = list(self.canvas.find_withtag('iqamah_instruction_text'))
        if not prayer_ids:
            return
        has_instruction = bool(instruction_ids)

        current_prayer_line = self.canvas.itemcget(prayer_ids[0], 'text')
        current_instruction_line = self.canvas.itemcget(instruction_ids[0], 'text') if has_instruction else ''

        if current_prayer_line == next_prayer_line and current_instruction_line == next_instruction_line:
            return

        prayer_bbox = self.canvas.bbox('iqamah_prayer_line_text')
        instruction_bbox = self.canvas.bbox('iqamah_instruction_text') if has_instruction else None
        if (not prayer_bbox) or (has_instruction and not instruction_bbox):
            for item_id in prayer_ids:
                self.canvas.itemconfig(item_id, text=next_prayer_line)
            if has_instruction:
                for item_id in instruction_ids:
                    self.canvas.itemconfig(item_id, text=next_instruction_line)
            return

        self._clear_iqamah_countdown_text_transition_artifacts()

        for item_id in prayer_ids:
            self.canvas.itemconfig(item_id, state='hidden')
        if has_instruction:
            for item_id in instruction_ids:
                self.canvas.itemconfig(item_id, state='hidden')

        self._iqamah_countdown_text_transition_payload = {
            'prayer_old': current_prayer_line,
            'prayer_new': next_prayer_line,
            'instruction_old': current_instruction_line,
            'instruction_new': next_instruction_line,
            'prayer_x': (prayer_bbox[0] + prayer_bbox[2]) / 2,
            'prayer_y': (prayer_bbox[1] + prayer_bbox[3]) / 2,
            'has_instruction': has_instruction,
            'instruction_x': ((instruction_bbox[0] + instruction_bbox[2]) / 2) if has_instruction else 0,
            'instruction_y': ((instruction_bbox[1] + instruction_bbox[3]) / 2) if has_instruction else 0,
            'progress': 0.0,
        }
        self._tick_iqamah_countdown_text_transition()

    def _tick_iqamah_countdown_text_transition(self):
        """Advance the iqamah countdown text language transition animation."""
        payload = getattr(self, '_iqamah_countdown_text_transition_payload', None)
        if not payload:
            return

        if not self.iqamah_overlay_visible or self.iqamah_overlay_mode != 'countdown':
            self._clear_iqamah_countdown_text_transition_artifacts()
            return

        try:
            self.canvas.delete('iqamah_countdown_lang_transition')
        except:
            pass
        self._iqamah_countdown_text_transition_temp_ids = []

        step = self.post_overlay_transition_tick_ms / max(1, self.post_overlay_transition_duration_ms)
        payload['progress'] = min(1.0, payload['progress'] + step)
        progress = payload['progress']
        eased = progress * progress * (3.0 - (2.0 * progress))

        travel = self.post_overlay_transition_travel
        has_instruction = payload.get('has_instruction', True)
        if eased < 0.5:
            # Phase 1: move old language out (no overlap with new text).
            phase = eased / 0.5
            outgoing_shift = -travel * phase
            prayer_out_id = self.canvas.create_text(
                payload['prayer_x'], payload['prayer_y'] + outgoing_shift,
                text=payload['prayer_old'],
                font=('Arial', self.fs(78, 34), 'bold'),
                fill='#2E7D32',
                tags=('iqamah_overlay', 'iqamah_countdown_lang_transition')
            )
            self._iqamah_countdown_text_transition_temp_ids.append(prayer_out_id)
            if has_instruction:
                instruction_out_id = self.canvas.create_text(
                    payload['instruction_x'], payload['instruction_y'] + outgoing_shift,
                    text=payload['instruction_old'],
                    font=('Arial', self.fs(68, 32), 'bold'),
                    fill='black',
                    tags=('iqamah_overlay', 'iqamah_countdown_lang_transition')
                )
                self._iqamah_countdown_text_transition_temp_ids.append(instruction_out_id)
        else:
            # Phase 2: move new language in after old language is gone.
            phase = (eased - 0.5) / 0.5
            incoming_shift = travel * (1.0 - phase)
            prayer_in_id = self.canvas.create_text(
                payload['prayer_x'], payload['prayer_y'] + incoming_shift,
                text=payload['prayer_new'],
                font=('Arial', self.fs(78, 34), 'bold'),
                fill='#2E7D32',
                tags=('iqamah_overlay', 'iqamah_countdown_lang_transition')
            )
            self._iqamah_countdown_text_transition_temp_ids.append(prayer_in_id)
            if has_instruction:
                instruction_in_id = self.canvas.create_text(
                    payload['instruction_x'], payload['instruction_y'] + incoming_shift,
                    text=payload['instruction_new'],
                    font=('Arial', self.fs(68, 32), 'bold'),
                    fill='black',
                    tags=('iqamah_overlay', 'iqamah_countdown_lang_transition')
                )
                self._iqamah_countdown_text_transition_temp_ids.append(instruction_in_id)
        self.canvas.tag_raise('iqamah_overlay')

        if progress >= 1.0:
            for item_id in self.canvas.find_withtag('iqamah_prayer_line_text'):
                self.canvas.itemconfig(item_id, text=payload['prayer_new'], state='normal')
            if has_instruction:
                for item_id in self.canvas.find_withtag('iqamah_instruction_text'):
                    self.canvas.itemconfig(item_id, text=payload['instruction_new'], state='normal')
            self._clear_iqamah_countdown_text_transition_artifacts()
            return

        self._iqamah_countdown_text_transition_after_id = self.root.after(
            self.iqamah_overlay_transition_tick_ms,
            self._tick_iqamah_countdown_text_transition
        )

    def _schedule_post_overlay_text_toggle(self):
        """Toggle instruction & prayer-now text between English and Arabic every 5s."""
        if not self.iqamah_overlay_visible or self.iqamah_overlay_mode != 'post':
            self._post_overlay_toggle_id = None
            return
        self._post_overlay_lang_english = not self._post_overlay_lang_english
        if self._post_overlay_lang_english:
            instr = 'Please put your cell phone on silent mode'
            pnow = 'Prayer is now'
        else:
            instr = 'يرجى وضع هاتفك على الوضع الصامت'
            pnow = 'الصلاة الآن'
        self._start_post_overlay_text_transition(instr, pnow)
        # English stays 10s, Arabic stays 5s
        delay = 10000 if self._post_overlay_lang_english else 5000
        self._post_overlay_toggle_id = self.root.after(delay, self._schedule_post_overlay_text_toggle)

    def _clear_post_overlay_text_transition_artifacts(self):
        """Cancel post overlay text transition and clear temporary layers."""
        transition_after_id = getattr(self, '_post_overlay_text_transition_after_id', None)
        if transition_after_id is not None:
            try:
                self.root.after_cancel(transition_after_id)
            except:
                pass
            self._post_overlay_text_transition_after_id = None

        try:
            self.canvas.delete('post_overlay_lang_transition')
        except:
            pass

        for item_id in getattr(self, '_post_overlay_text_transition_temp_ids', []):
            try:
                self.canvas.delete(item_id)
            except:
                pass
        self._post_overlay_text_transition_temp_ids = []
        self._post_overlay_text_transition_payload = None

    def _start_post_overlay_text_transition(self, next_instruction_line, next_prayer_now_line):
        """Animate post overlay instruction/prayer-now text with clean non-overlap slide."""
        if not self.iqamah_overlay_visible or self.iqamah_overlay_mode != 'post':
            return

        instruction_ids = list(self.canvas.find_withtag('post_instruction_text'))
        prayer_now_ids = list(self.canvas.find_withtag('post_prayer_now_text'))
        if not instruction_ids or not prayer_now_ids:
            return

        current_instruction_line = self.canvas.itemcget(instruction_ids[0], 'text')
        current_prayer_now_line = self.canvas.itemcget(prayer_now_ids[0], 'text')
        if current_instruction_line == next_instruction_line and current_prayer_now_line == next_prayer_now_line:
            return

        instruction_bbox = self.canvas.bbox('post_instruction_text')
        prayer_now_bbox = self.canvas.bbox('post_prayer_now_text')
        if not instruction_bbox or not prayer_now_bbox:
            for item_id in instruction_ids:
                self.canvas.itemconfig(item_id, text=next_instruction_line)
            for item_id in prayer_now_ids:
                self.canvas.itemconfig(item_id, text=next_prayer_now_line)
            return

        self._clear_post_overlay_text_transition_artifacts()

        for item_id in instruction_ids:
            self.canvas.itemconfig(item_id, state='hidden')
        for item_id in prayer_now_ids:
            self.canvas.itemconfig(item_id, state='hidden')

        self._post_overlay_text_transition_payload = {
            'instruction_old': current_instruction_line,
            'instruction_new': next_instruction_line,
            'prayer_old': current_prayer_now_line,
            'prayer_new': next_prayer_now_line,
            'instruction_x': (instruction_bbox[0] + instruction_bbox[2]) / 2,
            'instruction_y': (instruction_bbox[1] + instruction_bbox[3]) / 2,
            'prayer_x': (prayer_now_bbox[0] + prayer_now_bbox[2]) / 2,
            'prayer_y': (prayer_now_bbox[1] + prayer_now_bbox[3]) / 2,
            'progress': 0.0,
        }
        self._tick_post_overlay_text_transition()

    def _tick_post_overlay_text_transition(self):
        """Advance post overlay language transition without overlapping old/new text."""
        payload = getattr(self, '_post_overlay_text_transition_payload', None)
        if not payload:
            return

        if not self.iqamah_overlay_visible or self.iqamah_overlay_mode != 'post':
            self._clear_post_overlay_text_transition_artifacts()
            return

        try:
            self.canvas.delete('post_overlay_lang_transition')
        except:
            pass
        self._post_overlay_text_transition_temp_ids = []

        step = self.iqamah_overlay_transition_tick_ms / max(1, self.iqamah_overlay_transition_duration_ms)
        payload['progress'] = min(1.0, payload['progress'] + step)
        progress = payload['progress']
        eased = progress * progress * (3.0 - (2.0 * progress))

        travel = self.us(16, 8)
        if eased < 0.5:
            phase = eased / 0.5
            outgoing_shift = -travel * phase
            prayer_out_id = self.canvas.create_text(
                payload['prayer_x'], payload['prayer_y'] + outgoing_shift,
                text=payload['prayer_old'],
                font=('Arial', self.fs(92, 42), 'bold'),
                fill='#d32f2f',
                tags=('iqamah_overlay', 'post_overlay_lang_transition')
            )
            instruction_out_id = self.canvas.create_text(
                payload['instruction_x'], payload['instruction_y'] + outgoing_shift,
                text=payload['instruction_old'],
                font=('Arial', self.fs(62, 30), 'bold'),
                fill='black',
                tags=('iqamah_overlay', 'post_overlay_lang_transition')
            )
            self._post_overlay_text_transition_temp_ids.extend([prayer_out_id, instruction_out_id])
        else:
            phase = (eased - 0.5) / 0.5
            incoming_shift = travel * (1.0 - phase)
            prayer_in_id = self.canvas.create_text(
                payload['prayer_x'], payload['prayer_y'] + incoming_shift,
                text=payload['prayer_new'],
                font=('Arial', self.fs(92, 42), 'bold'),
                fill='#d32f2f',
                tags=('iqamah_overlay', 'post_overlay_lang_transition')
            )
            instruction_in_id = self.canvas.create_text(
                payload['instruction_x'], payload['instruction_y'] + incoming_shift,
                text=payload['instruction_new'],
                font=('Arial', self.fs(62, 30), 'bold'),
                fill='black',
                tags=('iqamah_overlay', 'post_overlay_lang_transition')
            )
            self._post_overlay_text_transition_temp_ids.extend([prayer_in_id, instruction_in_id])

        self.canvas.tag_raise('iqamah_overlay')

        if progress >= 1.0:
            for item_id in self.canvas.find_withtag('post_instruction_text'):
                self.canvas.itemconfig(item_id, text=payload['instruction_new'], state='normal')
            for item_id in self.canvas.find_withtag('post_prayer_now_text'):
                self.canvas.itemconfig(item_id, text=payload['prayer_new'], state='normal')
            self._clear_post_overlay_text_transition_artifacts()
            return

        self._post_overlay_text_transition_after_id = self.root.after(
            self.post_overlay_transition_tick_ms,
            self._tick_post_overlay_text_transition
        )

    def clear_iqamah_overlay_items(self):
        """Delete overlay canvas items while preserving overlay state variables."""
        try:
            # Cancel text toggle timers
            for attr in ('_post_overlay_toggle_id', '_iqamah_countdown_toggle_id'):
                toggle_id = getattr(self, attr, None)
                if toggle_id:
                    self.root.after_cancel(toggle_id)
                    setattr(self, attr, None)
            self._clear_iqamah_countdown_text_transition_artifacts()
            self._clear_post_overlay_text_transition_artifacts()
            for item_id in self.iqamah_overlay_ids:
                try:
                    self.canvas.delete(item_id)
                except:
                    pass
            # Safety purge: remove any overlay helper copies not tracked in iqamah_overlay_ids.
            try:
                self.canvas.delete('iqamah_overlay')
            except:
                pass
        finally:
            self.iqamah_overlay_ids = []
    
    def hide_iqamah_overlay(self):
        """Hide the Iqamah countdown overlay"""
        try:
            self.clear_iqamah_overlay_items()
            self.iqamah_overlay_visible = False
            if self.iqamah_overlay_mode == 'post':
                mocked_date = self.get_current_date()
                now_dt = datetime.combine(mocked_date, self.get_current_time())
                self.iqamah_overlay_cooldown_until = now_dt + timedelta(minutes=10)
            self.iqamah_overlay_mode = None
            self.current_prayer_iqamah_time = None
            self.current_prayer_name = None

            # Return to main screen immediately without waiting for next timer tick.
            try:
                self.redraw_full_display()
            except:
                pass

            # Restore prayer-change ribbon visibility state after overlay closes.
            if not self._ribbon_transition_running:
                state = 'normal' if self.ribbon_visible else 'hidden'
                try:
                    self.canvas.itemconfig('prayer_change_ribbon', state=state)
                except:
                    pass
            
        except Exception as e:
            self._log(f"ERROR in hide_iqamah_overlay: {e}")

    def draw_no_phone_icon(self, center_x, center_y, size=78, tags='iqamah_overlay'):
        """Draw a no-phone icon (phone + red prohibition ring/slash) and return canvas IDs."""
        item_ids = []

        radius = size / 2
        ring_id = self.canvas.create_oval(
            center_x - radius,
            center_y - radius,
            center_x + radius,
            center_y + radius,
            outline='#d32f2f',
            width=8,
            fill='',
            tags=tags
        )
        item_ids.append(ring_id)

        phone_w = size * 0.34
        phone_h = size * 0.56
        phone_x1 = center_x - (phone_w / 2)
        phone_y1 = center_y - (phone_h / 2)
        phone_x2 = center_x + (phone_w / 2)
        phone_y2 = center_y + (phone_h / 2)

        body_id = self.canvas.create_rectangle(
            phone_x1,
            phone_y1,
            phone_x2,
            phone_y2,
            fill='white',
            outline='black',
            width=3,
            tags=tags
        )
        item_ids.append(body_id)

        screen_pad_x = phone_w * 0.12
        screen_pad_y = phone_h * 0.16
        screen_id = self.canvas.create_rectangle(
            phone_x1 + screen_pad_x,
            phone_y1 + screen_pad_y,
            phone_x2 - screen_pad_x,
            phone_y2 - (screen_pad_y * 1.35),
            fill='#f3f3f3',
            outline='black',
            width=1,
            tags=tags
        )
        item_ids.append(screen_id)

        # Side vibration marks
        for mark_size in (0.28, 0.37, 0.46):
            arc_id = self.canvas.create_arc(
                center_x + (phone_w * 0.10),
                center_y - (size * mark_size),
                center_x + (size * mark_size),
                center_y + (size * mark_size),
                start=295,
                extent=70,
                style='arc',
                outline='black',
                width=3,
                tags=tags
            )
            item_ids.append(arc_id)

        slash_id = self.canvas.create_line(
            center_x - (radius * 0.72),
            center_y - (radius * 0.72),
            center_x + (radius * 0.72),
            center_y + (radius * 0.72),
            fill='#d32f2f',
            width=9,
            tags=tags
        )
        item_ids.append(slash_id)

        return item_ids
    
    def update_iqamah_overlay_countdown(self):
        """Update the countdown text on the overlay"""
        try:
            if self.iqamah_overlay_mode == 'khutbah':
                time_items = self.canvas.find_withtag('iqamah_overlay_current_time')
                if time_items:
                    new_time = self.get_current_time().strftime('%I:%M:%S %p')
                    self.canvas.itemconfig(time_items[0], text=new_time)
                bg_items = self.canvas.find_withtag('iqamah_overlay_time_bg')
                if bg_items:
                    self.canvas.tag_raise('iqamah_overlay_time_bg')
                    self.canvas.tag_raise('iqamah_overlay_current_time')
                return

            countdown = self.get_iqamah_countdown()

            # Hard transition: never remain on countdown overlay at 00:00
            if self.iqamah_overlay_mode == 'countdown' and countdown == '00:00':
                is_friday_jummah = (
                    self.current_prayer_name == 'Jummah'
                    and self.get_current_date().weekday() == 4
                )
                if is_friday_jummah:
                    self.hide_iqamah_overlay()
                    return
                if self.iqamah_post_duration_seconds > 0:
                    self.show_post_iqamah_overlay()
                    self.iqamah_overlay_visible = True
                    self.iqamah_overlay_mode = 'post'
                else:
                    self.hide_iqamah_overlay()
                return

            # Find and update the countdown text elements (includes outline copies)
            items = self.canvas.find_withtag('iqamah_countdown_time')
            for item in items:
                self.canvas.itemconfig(item, text=countdown)

            # Update current time on overlay (bottom-left)
            time_items = self.canvas.find_withtag('iqamah_overlay_current_time')
            if time_items:
                new_time = self.get_current_time().strftime('%I:%M:%S %p')
                self.canvas.itemconfig(time_items[0], text=new_time)
            bg_items = self.canvas.find_withtag('iqamah_overlay_time_bg')
            if bg_items:
                self.canvas.tag_raise('iqamah_overlay_time_bg')
                self.canvas.tag_raise('iqamah_overlay_current_time')

            # Keep Friday warning text synced to Arabic/English setting cadence.
            if self.iqamah_overlay_mode == 'countdown' and getattr(self, '_iqamah_countdown_is_friday', False):
                warning_items = self.canvas.find_withtag('iqamah_friday_warning_text')
                if warning_items:
                    try:
                        change_every_seconds = int(self.config.get('arabicchangeevery', 30))
                        change_every_seconds = max(1, change_every_seconds)
                    except:
                        change_every_seconds = 30
                    try:
                        arabic_duration_seconds = int(self.config.get('arabicnameduration', 10))
                        arabic_duration_seconds = max(0, arabic_duration_seconds)
                    except:
                        arabic_duration_seconds = 5
                    arabic_duration_seconds = min(arabic_duration_seconds, change_every_seconds)
                    now_dt = datetime.combine(self.get_current_date(), self.get_current_time())
                    seconds_into_cycle = int(now_dt.timestamp()) % change_every_seconds
                    warning_text = 'Talking is forbidden during Khutbahs'
                    if arabic_duration_seconds > 0 and seconds_into_cycle < arabic_duration_seconds:
                        warning_text = 'الكلام محرم اثناء الخطبتين'
                    for item_id in warning_items:
                        self.canvas.itemconfig(item_id, text=warning_text)

        except Exception as e:
            self._log(f"ERROR in update_iqamah_overlay_countdown: {e}")

    def get_iqamah_change_notice_text(self):
        """Return one-day-before iqamah change notice for current prayer, else None."""
        try:
            if not self.current_prayer_name:
                return None

            prayer_key = 'Duhr' if self.current_prayer_name == 'Jummah' else self.current_prayer_name
            if prayer_key == 'Maghrib':
                return None
            today_data = self.get_today_prayers() or {}
            tomorrow_data = self.get_tomorrow_prayers() or {}

            today_iqamah = (today_data.get(f'{prayer_key}Iqama', '') or '').strip()
            tomorrow_iqamah = (tomorrow_data.get(f'{prayer_key}Iqama', '') or '').strip()

            if not today_iqamah or not tomorrow_iqamah:
                return None

            if today_iqamah == '--' or tomorrow_iqamah == '--' or today_iqamah == tomorrow_iqamah:
                return None

            return tomorrow_iqamah
        except:
            return None
    
    def get_iqamah_countdown(self):
        """Get countdown text to Iqamah time in MM:SS format"""
        if not self.current_prayer_iqamah_time:
            return '00:00'
        
        try:
            current_time = self.get_current_time()
            mocked_date = self.get_current_date()
            now_dt = datetime.combine(mocked_date, current_time)
            iqamah_dt = datetime.combine(mocked_date, self.current_prayer_iqamah_time)
            
            diff = iqamah_dt - now_dt
            total_seconds = max(0, int(diff.total_seconds()))
            minutes, seconds = divmod(total_seconds, 60)
            
            return f"{minutes:02d}:{seconds:02d}"
        except Exception as e:
            self._log(f"ERROR in get_iqamah_countdown: {e}")
            return '00:00'
    
    def schedule_test_mode_update(self):
        """Schedule test mode indicator to update every second"""
        self.update_test_mode_indicator()
    
    def update_test_mode_indicator(self):
        """Update the test mode indicator time every second"""
        if not TEST_MODE:
            return
        
        try:
            # Find and update the test mode text objects
            width = self.canvas.winfo_width()
            current_time = self.get_current_time().strftime('%I:%M:%S %p')
            current_date = self.get_current_date()
            
            # Display test date and time on right
            test_info = f"Test Date: {current_date}  |  Time: {current_time}"
            box_height = 50

            if self.test_mode_box_id and self.test_mode_label_id and self.test_mode_info_id:
                self.canvas.coords(self.test_mode_box_id, 0, 0, width, box_height)
                self.canvas.coords(self.test_mode_label_id, 20, box_height/2)
                self.canvas.coords(self.test_mode_info_id, width - 20, box_height/2)
                self.canvas.itemconfig(self.test_mode_info_id, text=test_info)
            else:
                # Fallback after full redraw/deletion
                self.draw_test_mode_indicator()
        except:
            pass  # Silently fail if canvas operations fail
        
        # Schedule next update in 1000ms (1 second)
        try:
            self.root.after(1000, self.update_test_mode_indicator)
        except:
            pass
    
    def draw_header(self, width, height):
        """Draw the Islamic center title and address at top center"""
        palette = self.get_theme_palette()
        # Get masjid name and address from config
        masjid_name = self.config.get('masjid_name', 'MASJID')
        address = self.config.get('location', 'Address')

        # Show date at the former masjid-name position.
        current_date = self.get_current_date()
        show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))

        english_day_text = current_date.strftime('%A')
        english_miladi_text = current_date.strftime('%B %d, %Y')
        arabic_weekdays = {
            0: 'الاثنين',
            1: 'الثلاثاء',
            2: 'الأربعاء',
            3: 'الخميس',
            4: 'الجمعة',
            5: 'السبت',
            6: 'الأحد'
        }
        arabic_months = {
            1: 'يناير', 2: 'فبراير', 3: 'مارس', 4: 'أبريل',
            5: 'مايو', 6: 'يونيو', 7: 'يوليو', 8: 'أغسطس',
            9: 'سبتمبر', 10: 'أكتوبر', 11: 'نوفمبر', 12: 'ديسمبر'
        }
        arabic_day_text = arabic_weekdays.get(current_date.weekday(), english_day_text)
        arabic_miladi_text = f"{current_date.day} {arabic_months.get(current_date.month, '')} {current_date.year}"

        day_text = arabic_day_text if show_arabic_name else english_day_text
        miladi_text = arabic_miladi_text if show_arabic_name else english_miladi_text
        if Gregorian:
            try:
                hijri = Gregorian(current_date.year, current_date.month, current_date.day).to_hijri()
                english_hijri_text = f"{hijri.day} {self.get_hijri_month_name(hijri.month)} {hijri.year}H"
                arabic_hijri_months = {
                    1: 'محرم', 2: 'صفر', 3: 'ربيع الأول', 4: 'ربيع الآخر',
                    5: 'جمادى الأولى', 6: 'جمادى الآخرة', 7: 'رجب', 8: 'شعبان',
                    9: 'رمضان', 10: 'شوال', 11: 'ذو القعدة', 12: 'ذو الحجة'
                }
                arabic_hijri_text = f"{hijri.day} {arabic_hijri_months.get(hijri.month, '')} {hijri.year}هـ"
                hijri_text = arabic_hijri_text if show_arabic_name else english_hijri_text
            except:
                hijri_text = 'التاريخ الهجري غير متاح' if show_arabic_name else 'Hijri date unavailable'
        else:
            hijri_text = 'التاريخ الهجري غير متاح' if show_arabic_name else 'Hijri date unavailable'

        date_font = ('Arial', self.fs(42, 24), 'bold') if show_arabic_name else ('Arial', self.fs(36, 20), 'bold')
        self.draw_outlined_text(
            width / 2, self.us(185),
            text=f"{day_text} | {hijri_text} | {miladi_text}",
            font=date_font,
            fill='white',
            outline='black',
            outline_px=self.us(3, 2),
            anchor='center'
        )

    def draw_top_right_logo(self, width, height):
        """Draw the configured logo image at the top-right and top-left corners."""
        if not getattr(self, 'show_logo', False):
            return
        try:
            logo_w = int(self.config.get('logo_width', 420))
            logo_h = int(self.config.get('logo_height', 280))
            target_size = (self.us(logo_w), self.us(logo_h))
            # Resolve images dir: prefer folder next to exe (frozen) or cwd, then source dir
            images_dir = None
            if getattr(sys, 'frozen', False):
                exe_images = Path(sys.executable).resolve().parent.parent / 'images'
                if not exe_images.is_dir():
                    exe_images = Path(sys.executable).resolve().parent / 'images'
                if exe_images.is_dir():
                    images_dir = exe_images
            if images_dir is None:
                cwd_images = Path.cwd() / 'images'
                if cwd_images.is_dir():
                    images_dir = cwd_images
            if images_dir is None:
                images_dir = Path(__file__).resolve().parent / 'images'
            primary_path = images_dir / 'main.png'
            fallback_path = images_dir / 'main.jpg'
            image_path = primary_path if primary_path.exists() else fallback_path

            if image_path.exists():
                current_mtime = image_path.stat().st_mtime
                if (self.logo_base_image is None or self.logo_image_path != str(image_path)
                        or self.logo_image_size != target_size or self.logo_image_mtime != current_mtime):
                    with Image.open(image_path) as img:
                        self.logo_base_image = img.convert('RGBA').resize(target_size, Image.LANCZOS)
                        self.logo_image_size = target_size
                        self.logo_image_path = str(image_path)
                        self.logo_image_mtime = current_mtime

                if self.logo_base_image is not None:
                    self.logo_image_tk = ImageTk.PhotoImage(self.logo_base_image)
            else:
                # Image file was deleted — clear cached logo
                self.logo_base_image = None
                self.logo_image_tk = None
                self.logo_image_path = None
                self.logo_image_mtime = None
                return

            if self.logo_image_tk is not None:
                image_w, image_h = target_size
                logo_x_offset = int(self.config.get('logo_x_offset', -30))
                scaled_logo_x_offset = int(round(logo_x_offset * self.ui_scale))

                logo_center_x = (image_w / 2) + scaled_logo_x_offset
                logo_center_y = height + self.us(116) - (image_h / 2)

                self.canvas.create_image(
                    logo_center_x,
                    logo_center_y,
                    image=self.logo_image_tk,
                    anchor='center'
                )

                if self.is_ramadan(self.get_current_date()):
                    calligraphy_candidates = ['Segoe Script', 'Lucida Handwriting', 'Brush Script MT']
                    calligraphy_font = next(
                        (font_name for font_name in calligraphy_candidates if font_name in tkfont.families()),
                        'Arial'
                    )
                    text_y = logo_center_y + (image_h / 2) + self.us(18, 8)

                    self.draw_outlined_text(
                        logo_center_x,
                        text_y,
                        text='Ramadhan Mubarak',
                        font=(calligraphy_font, self.fs(20, 10), 'bold'),
                        fill='#d4af37',
                        outline='black',
                        outline_px=self.us(2, 1),
                        anchor='center'
                    )
        except Exception as e:
            self._log(f"ERROR in draw_top_right_logo: {e}")

    def draw_outlined_text(self, x, y, text, font, fill='white', outline='black', outline_px=2, **kwargs):
        """Draw text with a simple outline by layering offset shadow copies."""
        if outline and outline_px > 0:
            offsets = [
                (-outline_px, -outline_px), (-outline_px, 0), (-outline_px, outline_px),
                (0, -outline_px), (0, outline_px),
                (outline_px, -outline_px), (outline_px, 0), (outline_px, outline_px)
            ]

            for dx, dy in offsets:
                self.canvas.create_text(
                    x + dx, y + dy,
                    text=text,
                    font=font,
                    fill=outline,
                    **kwargs
                )

        return self.canvas.create_text(
            x, y,
            text=text,
            font=font,
            fill=fill,
            **kwargs
        )
    
    def draw_date_info(self, width, height):
        """Draw current date and day - now drawn at new position under translation"""
        pass
    
    def draw_date_info_at_position(self, x, y):
        """Draw current date and day at specified position"""
        now = datetime.combine(self.get_current_date(), datetime.min.time())
        
        # Day name
        day_name = now.strftime('%A')
        
        # Miladi date in readable format
        date_str = now.strftime('%B %d, %Y')
        
        # Hijri date
        try:
            gregorian = Gregorian(now.year, now.month, now.day)
            hijri = gregorian.to_hijri()
            hijri_str = f"{hijri.day} {self.get_hijri_month_name(hijri.month)} {hijri.year}H"
        except:
            hijri_str = "Hijri date"
        
        # Draw day name
        self.draw_outlined_text(
            x, y,
            text=day_name,
            font=('Arial', self.fs(34, 15), 'bold'),
            fill='white',
            outline='black',
            outline_px=self.us(3, 2),
            anchor='center'
        )
        
        # Draw Miladi date
        self.draw_outlined_text(
            x, y + self.us(60, 30),
            text=date_str,
            font=('Arial', self.fs(22, 11)),
            fill='white',
            outline='black',
            outline_px=self.us(3, 2),
            anchor='center'
        )
        
        # Draw Hijri date
        self.draw_outlined_text(
            x, y + self.us(95, 50),
            text=hijri_str,
            font=('Arial', self.fs(22, 11)),
            fill='white',
            outline='black',
            outline_px=self.us(3, 2),
            anchor='center'
        )
    
    def get_hijri_month_name(self, month):
        """Get Hijri month name"""
        hijri_months = [
            'Muharram', 'Safar', 'Rabil Al-Awwal', 'Rabil Al-Thani',
            'Jumada Al-Awwal', 'Jumada Al-Thani', 'Rajab', 'Sha\'ban',
            'Ramadan', 'Shawwal', 'Dhu Al-Qi\'dah', 'Dhu Al-Hijjah'
        ]
        return hijri_months[month - 1] if 1 <= month <= 12 else 'Unknown'

    # ── Weather Methods ──────────────────────────────────────────────

    def _get_weather_icon(self, code):
        """Map WMO weather code to emoji icon."""
        if code == 0:
            return '☀'
        elif code in (1, 2):
            return '⛅'
        elif code == 3:
            return '☁'
        elif code in (45, 48):
            return '🌫'
        elif code in (51, 53, 55, 61, 63, 65, 80, 81, 82):
            return '🌧'
        elif code in (71, 73, 75, 77, 85, 86):
            return '❄'
        elif code in (95, 96, 99):
            return '⛈'
        return '☁'

    def _get_weather_desc(self, code):
        """Map WMO weather code to short description."""
        descs = {
            0: 'Clear', 1: 'Mostly Clear', 2: 'Partly Cloudy', 3: 'Overcast',
            45: 'Foggy', 48: 'Icy Fog',
            51: 'Light Drizzle', 53: 'Drizzle', 55: 'Heavy Drizzle',
            61: 'Light Rain', 63: 'Rain', 65: 'Heavy Rain',
            71: 'Light Snow', 73: 'Snow', 75: 'Heavy Snow', 77: 'Snow Grains',
            80: 'Light Showers', 81: 'Showers', 82: 'Heavy Showers',
            85: 'Snow Showers', 86: 'Heavy Snow Showers',
            95: 'Thunderstorm', 96: 'Thunderstorm', 99: 'Thunderstorm'
        }
        return descs.get(code, 'Cloudy')

    def _geocode_address(self, address):
        """Geocode address using Nominatim. Returns (lat, lon) or (None, None)."""
        try:
            parts = [p.strip() for p in address.split(',')]
            # Build query: city, province (strip postal code), Canada
            if len(parts) >= 3:
                province = parts[2].strip().split()[0]  # e.g. "ON N8T 1B4" -> "ON"
                query = f"{parts[1].strip()}, {province}, Canada"
            elif len(parts) >= 2:
                query = f"{parts[1].strip()}, Canada"
            else:
                query = address
            url = 'https://nominatim.openstreetmap.org/search?q=' + urllib.parse.quote(query) + '&format=json&limit=1'
            req = urllib.request.Request(url, headers={'User-Agent': 'PrayerTimeDisplay/1.0'})
            with urllib.request.urlopen(req, timeout=10) as resp:
                data = json.loads(resp.read().decode('utf-8'))
            if data:
                return float(data[0]['lat']), float(data[0]['lon'])
        except Exception as e:
            self._log(f"[WEATHER] Geocode error: {e}")
        return None, None

    def _fetch_weather_data(self):
        """Fetch current weather + 2-day forecast using Nominatim + Open-Meteo."""
        try:
            address = self.config.get('location', '')
            if not address:
                return

            # Geocode once, cache coordinates
            if not getattr(self, '_weather_lat', None):
                lat, lon = self._geocode_address(address)
                if lat is None:
                    self._log("[WEATHER] Geocoding failed")
                    return
                self._weather_lat = lat
                self._weather_lon = lon

            lat = self._weather_lat
            lon = self._weather_lon

            url = (f'https://api.open-meteo.com/v1/forecast'
                   f'?latitude={lat}&longitude={lon}'
                   f'&current=temperature_2m,weather_code'
                     f'&hourly=weather_code,precipitation_probability'
                   f'&daily=weather_code,temperature_2m_max,temperature_2m_min'
                   f'&timezone=auto&forecast_days=3')
            with urllib.request.urlopen(url, timeout=15) as resp:
                data = json.loads(resp.read().decode('utf-8'))

            curr = data['current']
            current_temp = round(curr['temperature_2m'])
            current_code = curr['weather_code']
            current_icon = self._get_weather_icon(current_code)
            current_desc = self._get_weather_desc(current_code)

            daily = data['daily']
            hourly = data.get('hourly', {})
            hourly_times = hourly.get('time', []) or []
            hourly_codes = hourly.get('weather_code', []) or []
            hourly_pops = hourly.get('precipitation_probability', []) or []

            # Build daytime hourly buckets for each day.
            midday_code_by_day = {}
            daytime_codes_by_day = {}
            daytime_popmax_by_day = {}
            precip_codes = {
                51, 53, 55, 56, 57, 61, 63, 65, 66, 67,
                71, 73, 75, 77, 80, 81, 82, 85, 86,
                95, 96, 99
            }
            for idx, ts in enumerate(hourly_times):
                if idx >= len(hourly_codes):
                    break
                if not ts or len(ts) < 13:
                    continue

                day_key = ts[:10]
                hour_str = ts[11:13]
                try:
                    hour_val = int(hour_str)
                except:
                    continue

                code_val = hourly_codes[idx]

                if hour_val == 12 and day_key not in midday_code_by_day:
                    midday_code_by_day[day_key] = code_val

                if 6 <= hour_val <= 21:
                    daytime_codes_by_day.setdefault(day_key, []).append(code_val)
                    pop_val = 0
                    if idx < len(hourly_pops):
                        try:
                            pop_val = int(hourly_pops[idx])
                        except:
                            pop_val = 0
                    prev_pop = daytime_popmax_by_day.get(day_key, 0)
                    if pop_val > prev_pop:
                        daytime_popmax_by_day[day_key] = pop_val

            forecast = []
            for i in range(1, 3):  # skip today (index 0), take next 2 days
                try:
                    dt = datetime.strptime(daily['time'][i], '%Y-%m-%d')
                    day_name = dt.strftime('%a')
                except:
                    day_name = daily['time'][i]
                day_key = daily['time'][i]
                daily_code = daily['weather_code'][i]
                day_codes = daytime_codes_by_day.get(day_key, [])
                precip_hits = [c for c in day_codes if c in precip_codes]
                day_popmax = daytime_popmax_by_day.get(day_key, 0)

                if daily_code in precip_codes and day_popmax >= 35:
                    code = daily_code
                elif len(precip_hits) >= 2:
                    code = precip_hits[0]
                else:
                    code = midday_code_by_day.get(day_key, daily_code)
                forecast.append({
                    'day': day_name,
                    'high': round(daily['temperature_2m_max'][i]),
                    'low': round(daily['temperature_2m_min'][i]),
                    'icon': self._get_weather_icon(code)
                })

            self.weather_data = {
                'current_temp': current_temp,
                'current_icon': current_icon,
                'current_desc': current_desc,
                'forecast': forecast
            }
            self.weather_last_fetch = time.time()
            self._log(f"[WEATHER] Updated: {current_temp}C, {current_desc}")
            try:
                self.root.after(0, self.redraw_full_display)
            except:
                pass
        except Exception as e:
            self._log(f"[WEATHER] Fetch error: {e}")
            if self.weather_data is not None:
                self.weather_data = None
                try:
                    self.root.after(0, self.redraw_full_display)
                except:
                    pass
        finally:
            self._weather_fetching = False

    def _start_weather_fetch(self):
        """Start a background weather fetch and schedule the next one."""
        if self.show_weather and not self._weather_fetching:
            now = time.time()
            if now - self.weather_last_fetch >= self.weather_fetch_interval or self.weather_data is None:
                self._weather_fetching = True
                t = threading.Thread(target=self._fetch_weather_data, daemon=True)
                t.start()
        # Schedule next check
        try:
            self.root.after(60000, self._start_weather_fetch)  # Check every 60 seconds
        except:
            pass

    def _weather_has_active_rain(self):
        """Return True when current or forecast cards include rain/thunder icons."""
        if not self.show_weather or not self.weather_data:
            return False

        icons = [self.weather_data.get('current_icon', '')]
        forecast = self.weather_data.get('forecast', [])
        for day in forecast[:2]:
            icons.append(day.get('icon', ''))

        return any(icon in ('🌧', '⛈') for icon in icons)

    def _schedule_weather_animation(self):
        """Drive smooth weather animation independently from 1-second clock updates."""
        try:
            if self._weather_has_active_rain() and not self.iqamah_overlay_visible and not self._np_anim_active:
                self.redraw_full_display()
                delay = self._weather_anim_interval_ms
            else:
                delay = 350

            self._weather_anim_after_id = self.root.after(delay, self._schedule_weather_animation)
        except:
            pass

    def draw_weather(self, width, height):
        """Draw weather as 3 compact horizontal cards under current time."""
        if not self.weather_data:
            return

        card_h = self.us(118, 62)
        card_w = self.us(272, 150)
        card_gap = self.us(12, 7)
        padding_x = self.us(16, 9)
        corner_r = self.us(14, 8)
        weather_y_offset = -self.us(10, 6)

        # Icon color mapping
        icon_colors = {
            '☀': '#FFD700',   # gold / sun
            '⛅': '#FFB347',   # orange / partly cloudy
            '☁': '#B0C4DE',   # light steel blue / cloudy
            '🌫': '#A9A9A9',   # grey / fog
            '🌧': '#6CB4EE',   # light blue / rain
            '❄': '#E0FFFF',    # ice blue / snow
            '⛈': '#DA70D6',   # orchid / thunderstorm
        }

        card_bg_by_icon = {
            '☀': (78, 58, 6),
            '⛅': (74, 48, 12),
            '☁': (28, 40, 62),
            '🌫': (48, 48, 48),
            '🌧': (10, 58, 98),
            '❄': (18, 72, 88),
            '⛈': (58, 26, 82),
        }

        # Build card data: (label, icon, temp_text)
        cards = []
        cards.append((
            'Now',
            self.weather_data.get('current_icon', '☁'),
            f"{self.weather_data.get('current_temp', '--')}°C"
        ))

        forecast = self.weather_data.get('forecast', [])
        for day in forecast[:2]:
            cards.append((
                day.get('day', '--'),
                day.get('icon', '☁'),
                f"{day.get('high', '--')}° / {day.get('low', '--')}°"
            ))

        card_count = max(1, len(cards))
        total_w = (card_count * card_w) + ((card_count - 1) * card_gap)

        if self.get_theme_name() == 'elegent_v2':
            left_panel_x = self.us(36, 18)
            left_panel_w = min(self.us(880, 550), max(self.us(590, 360), width * 0.50))
            right_area_x1 = left_panel_x + left_panel_w + self.us(26, 16)
            right_area_w = max(self.us(320, 200), width - right_area_x1 - self.us(34, 18))
            right_center_x = right_area_x1 + (right_area_w / 2)
            x_start = right_center_x - (total_w / 2)
            y_start = self.jummah_box_y + self.jummah_box_h + self.us(12, 8) + weather_y_offset
            min_x = right_area_x1 + self.us(4, 2)
            max_x = right_area_x1 + right_area_w - total_w - self.us(4, 2)
            x_start = max(min_x, min(max_x, x_start))
        else:
            aligned_right = None
            if self.current_time_text_id:
                try:
                    time_bbox = self.canvas.bbox(self.current_time_text_id)
                    if time_bbox and len(time_bbox) >= 4:
                        aligned_right = time_bbox[2]
                except Exception:
                    aligned_right = None

            if aligned_right is None and self.current_time_outline_ids:
                try:
                    outline_right_edges = []
                    for oid in self.current_time_outline_ids:
                        ob = self.canvas.bbox(oid)
                        if ob and len(ob) >= 4:
                            outline_right_edges.append(ob[2])
                    if outline_right_edges:
                        aligned_right = max(outline_right_edges)
                except Exception:
                    aligned_right = None

            if aligned_right is not None:
                x_start = aligned_right - total_w
            else:
                x_start = width - total_w - self.us(20, 10)
            y_start = height - card_h - self.us(45, 22) + weather_y_offset

        # Keep references to prevent garbage collection
        if not hasattr(self, '_weather_row_images'):
            self._weather_row_images = []
        self._weather_row_images.clear()

        label_font = self.fs(26, 14)
        icon_font = self.fs(32, 17)
        temp_font = self.fs(44, 24)
        label_font_spec = ('Arial', label_font, 'bold')
        temp_color_now = '#ffffff'
        temp_color_forecast = '#ffffff'

        for i, (label, icon, temp_text) in enumerate(cards):
            rx = x_start + i * (card_w + card_gap)

            # Semi-transparent rounded card background
            try:
                bg_img = Image.new('RGBA', (card_w, card_h), (0, 0, 0, 0))
                draw = ImageDraw.Draw(bg_img)
                r = corner_r
                # Match each card background to its weather condition.
                base_rgb = card_bg_by_icon.get(icon, (20, 40, 70))
                alpha = 195 if i == 0 else 178
                bg_color = (base_rgb[0], base_rgb[1], base_rgb[2], alpha)
                draw.rounded_rectangle(
                    [(0, 0), (card_w - 1, card_h - 1)],
                    radius=r, fill=bg_color
                )

                # Add visible weather effects so each card reads instantly.
                if icon in ('🌧', '⛈'):
                    rain_step_x = self.us(24, 13)
                    rain_step_y = self.us(34, 18)
                    drop_len = self.us(12, 7)
                    drop_slant = self.us(4, 2)
                    rain_top = self.us(34, 20)
                    rain_bottom = card_h - self.us(10, 6)
                    rain_height = max(1, rain_bottom - rain_top)
                    phase = int((time.time() * 70) % rain_height)

                    for lane_x in range(-self.us(20, 12), card_w + self.us(20, 12), rain_step_x):
                        lane_offset = (lane_x * 7) % rain_height
                        y = rain_top + ((phase + lane_offset) % rain_height)
                        while y > rain_top:
                            y0 = y
                            y1 = max(rain_top, y - drop_len)
                            x0 = lane_x
                            x1 = lane_x - drop_slant
                            tip_r = max(1, self.us(2, 1))

                            # Teardrop look: bright rounded head + trailing tail.
                            draw.ellipse(
                                [(x0 - tip_r, y0 - tip_r), (x0 + tip_r, y0 + tip_r)],
                                fill=(196, 238, 255, 240)
                            )
                            draw.line(
                                [(x0, y0), (x1, y1)],
                                fill=(170, 230, 255, 225),
                                width=max(1, self.us(2, 1))
                            )
                            y -= rain_step_y
                elif icon == '❄':
                    flake_step = self.us(28, 16)
                    for sx in range(self.us(16, 9), card_w - self.us(18, 10), flake_step):
                        for sy in range(self.us(46, 26), card_h - self.us(14, 8), self.us(24, 14)):
                            rr = max(1, self.us(3, 2))
                            draw.ellipse(
                                [(sx - rr, sy - rr), (sx + rr, sy + rr)],
                                fill=(240, 252, 255, 230)
                            )
                elif icon in ('☀', '⛅'):
                    sun_cx = card_w - self.us(42, 24)
                    sun_cy = self.us(30, 17)
                    sun_r = self.us(16, 9)
                    draw.ellipse(
                        [(sun_cx - sun_r, sun_cy - sun_r), (sun_cx + sun_r, sun_cy + sun_r)],
                        fill=(255, 214, 64, 220)
                    )
                    for ray in range(0, 360, 45):
                        a = math.radians(ray)
                        r0 = sun_r + self.us(4, 2)
                        r1 = sun_r + self.us(10, 6)
                        x0 = sun_cx + math.cos(a) * r0
                        y0 = sun_cy + math.sin(a) * r0
                        x1 = sun_cx + math.cos(a) * r1
                        y1 = sun_cy + math.sin(a) * r1
                        draw.line([(x0, y0), (x1, y1)], fill=(255, 224, 110, 215), width=max(1, self.us(2, 1)))
                tk_img = ImageTk.PhotoImage(bg_img)
                self._weather_row_images.append(tk_img)
                self.canvas.create_image(
                    rx, y_start, image=tk_img, anchor='nw',
                    tags='weather_row'
                )
            except Exception:
                pass

            # Label near top-left
            self.canvas.create_text(
                rx + padding_x, y_start + self.us(22, 12),
                text=label,
                font=label_font_spec,
                fill='#ffffff',
                anchor='w',
                tags='weather_row'
            )

            # Icon sits next to the label (Now / forecast day)
            icon_color = icon_colors.get(icon, '#ffffff')
            label_w = tkfont.Font(font=label_font_spec).measure(f"{label} ")
            self.canvas.create_text(
                rx + padding_x + label_w, y_start + self.us(22, 12),
                text=icon,
                font=('Segoe UI Emoji', icon_font),
                fill=icon_color,
                anchor='w',
                tags='weather_row'
            )

            # Temperature on right side
            self.canvas.create_text(
                rx + card_w - padding_x, y_start + card_h - self.us(30, 16),
                text=temp_text,
                font=('Arial', temp_font, 'bold'),
                fill=temp_color_now if i == 0 else temp_color_forecast,
                anchor='e',
                tags='weather_row'
            )

    def _set_weather_group_state(self, tag, state):
        """Set all canvas items with given tag to state ('normal' or 'hidden')."""
        for item_id in self.canvas.find_withtag(tag):
            self.canvas.itemconfig(item_id, state=state)

    def _start_weather_cycle(self):
        """No-op: weather rows are always visible now."""
        pass

    def _weather_cycle_step(self):
        """No-op: weather rows are always visible now."""
        pass

    def _weather_fade_out(self, step=0):
        """No-op: weather rows are always visible now."""
        pass

    def _weather_fade_in(self, tag, step=0):
        """No-op: weather rows are always visible now."""
        pass

    def draw_quran_verse(self, width, height):
        """Draw Quranic verse above prayer times with translation"""
        palette = self.get_theme_palette()
        # Arabic verse: "Verily, as-Salat (the prayer) is enjoined on the believers at fixed hours" (An-Nisa 4:103)
        verse = "﴾ إِنَّ الصَّلَاةَ كَانَتْ عَلَى الْمُؤْمِنِينَ كِتَابًا مَوْقُوتًا ﴿"
        translation = "Prayer has been decreed upon the believers at specific times."
        
        # Ayah at top, translation below, masjid name drawn in draw_header
        arabic_font_size = self.fs(62, 28)
        verse_text_y = self.us(55)
        self.draw_outlined_text(
            width / 2, verse_text_y,
            text=verse,
            font=('Arial', arabic_font_size, 'bold'),
            fill='#d4af37',  # Gold color for Arabic text
            outline='black',
            outline_px=self.us(2, 1),
            anchor='center',
            justify='center'
        )
        
        # Draw the English translation text below the ayah
        translation_y = self.us(120)
        self.draw_outlined_text(
            width / 2, translation_y,
            text=translation,
            font=('Arial', self.fs(32, 16)),
            fill='#ffffff',  # White color for translation
            outline='black',
            outline_px=self.us(1, 1),
            anchor='center',
            justify='center'
        )
    
    def draw_prayer_times(self):
        """Draw prayer time boxes with error handling"""
        try:
            return self._draw_prayer_times_impl()
        except Exception as e:
            self._log(f"ERROR in draw_prayer_times: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()
            return
    
    def _draw_prayer_times_impl(self):
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        
        if width <= 1 or height <= 1:
            return

        self.set_ui_scale(width, height)

        self.next_prayer_panel_height = self.us(94, 56)
        self.next_prayer_panel_radius = self.us(36, 20)
        self.next_prayer_panel_padding_x = self.us(44, 20)
        line_font_size = self.fs(46, 22)
        prefix_font_size = max(12, line_font_size - self.fs(8, 4))
        if int(self.next_prayer_line_font.cget('size')) != line_font_size:
            self.next_prayer_line_font.configure(size=line_font_size)
            self.next_prayer_prefix_font.configure(size=prefix_font_size)
            self.next_prayer_countdown_fixed_width = self.next_prayer_line_font.measure('88:88:88')
        
        prayers_data = self.get_today_prayers()
        if not prayers_data:
            return
        
        # Check for upcoming changes first (3+ days ahead)
        self.check_upcoming_changes()
        
        # Check which prayers will change tomorrow
        self.check_prayer_changes()
        
        # Draw title and date at top
        self.draw_header(width, height)

        # Draw Quranic verse above prayer times
        self.draw_quran_verse(width, height)

        # Define prayers to display
        prayers = [
            ('Fajr', 'Fajr', 'الفجر'),
            ('Dhuhr', 'Duhr', 'الظهر'),
            ('Asr', 'Asr', 'العصر'),
            ('Maghrib', 'Maghrib', 'المغرب'),
            ('Isha', 'Isha', 'العشاء')
        ]
        prayers_with_shrouq = prayers[:1] + [('Shrouq', 'Shrouq', 'الشروق')] + prayers[1:]
        prayers_with_shrouq_jummah = prayers_with_shrouq + [('Jummah', 'Jummah', 'الجمعة')]

        # Reset box shape tracking for current frame
        self.prayer_box_shape_ids = {}
        self.prayer_box_bounds = {}
        
        # Get current prayer
        current_prayer = self.get_current_prayer(prayers_data)
        self.last_rendered_current_prayer = current_prayer

        theme_name = self.get_theme_name()
        if theme_name == 'elegent_v2':
            self.draw_elegent_v2_left_prayer_table(width, height, prayers_data, prayers_with_shrouq_jummah, current_prayer)
            if self.show_weather and self.weather_data:
                self.draw_weather(width, height)
            self.draw_top_right_logo(width, height)
            if self.is_eid_day(self.get_current_date()):
                self.canvas.delete('animated_eid')
                self.draw_eid_fireworks(width, height, animated=True, tags='animated_eid')
                self.draw_eid_balloons(width, height, animated=True, tags='animated_eid')
                self.canvas.tag_raise('animated_eid')
            self.draw_build_info(width, height)
            return

        if theme_name == 'elegent':
            self.draw_elegent_compact_prayer_table(width, height, prayers_data, prayers_with_shrouq, current_prayer)
            if self.show_weather and self.weather_data:
                self.draw_weather(width, height)
            self.draw_build_info(width, height)
            return
        
        # Calculate box dimensions - all same size
        box_width = self.us(320, 190)
        box_height = self.us(255, 155)
        lower_row_box_height = box_height
        spacing = self.us(30, 15)
        
        # Calculate total width
        total_width = (box_width * 5) + (spacing * 4)
        
        start_x = (width - total_width) / 2
        # Position prayer boxes below current time display
        center_y = self.us(420, 310)
        
        # Store lower-row box positions for standalone current-time placement
        next_prayer_box_x = None
        next_prayer_box_y = None
        next_prayer_box_h = None
        jummah_box_x = None
        jummah_box_y = None
        jummah_box_h = None
        next_prayer_name_for_display = None
        
        # Draw each prayer box
        x_offset = 0
        lower_row_offset = self.us(10, 6)
        for idx, (display_name, key, arabic) in enumerate(prayers):
            is_current = (key == current_prayer)
            
            box_w = box_width
            box_h = box_height
            
            x = start_x + x_offset
            y = center_y - (box_h / 2)
            
            # Get prayer times
            athan_time = prayers_data.get(f'{key}Athan', '--')
            iqamah_time = prayers_data.get(f'{key}Iqama', '--')
            
            # Add AM to Fajr times if not already present
            if key == 'Fajr':
                if athan_time != '--' and 'AM' not in athan_time and 'PM' not in athan_time:
                    athan_time = athan_time + ' AM'
                if iqamah_time != '--' and 'AM' not in iqamah_time and 'PM' not in iqamah_time:
                    iqamah_time = iqamah_time + ' AM'
            
            tomorrow_iqamah_time = None
            show_red_ribbon = False
            
            # Check if this prayer changes tomorrow (1 day before)
            # Red ribbon shows the new time that will take effect at midnight
            if key in self.changing_prayers:
                change_info = self.changing_prayers[key]
                tomorrow_iqamah_time = change_info['tomorrow_iqama']
                # Add AM to Fajr tomorrow time if not already present
                if key == 'Fajr' and tomorrow_iqamah_time and tomorrow_iqamah_time != '--':
                    if 'AM' not in tomorrow_iqamah_time and 'PM' not in tomorrow_iqamah_time:
                        tomorrow_iqamah_time = tomorrow_iqamah_time + ' AM'
                show_red_ribbon = True
            
            box_shape_id = self.draw_prayer_box(x, y, box_w, box_h, 
                               display_name, arabic, athan_time, iqamah_time, is_current, 
                               show_tomorrow_iqamah=show_red_ribbon, prayer_key=key, 
                               tomorrow_iqamah=tomorrow_iqamah_time)
            if box_shape_id:
                self.prayer_box_shape_ids[key] = box_shape_id
                self.prayer_box_bounds[key] = (x, y, box_w, box_h)
            
            # Draw Shouruq box below Fajr
            if idx == 0:
                next_prayer, next_athan = self.get_next_prayer(prayers_data)
                next_prayer_name_for_display = next_prayer
                self.next_prayer_athan_time = next_athan
                next_prayer_box_x = x
                next_prayer_box_y = y + box_h + lower_row_offset
                next_prayer_box_h = lower_row_box_height
                sunrise_time, _ = self.resolve_sunrise_time(prayers_data)
                if sunrise_time != '--' and 'AM' not in sunrise_time and 'PM' not in sunrise_time:
                    sunrise_time = sunrise_time + ' AM'
                is_shrouq_current = (current_prayer == 'Shrouq')
                shrouq_shape_id = self.draw_shouruq_box(
                    next_prayer_box_x,
                    next_prayer_box_y,
                    box_width,
                    next_prayer_box_h,
                    sunrise_time,
                    is_current=is_shrouq_current
                )
                if shrouq_shape_id:
                    self.prayer_box_shape_ids['Shrouq'] = shrouq_shape_id
                    self.prayer_box_bounds['Shrouq'] = (next_prayer_box_x, next_prayer_box_y, box_width, next_prayer_box_h)
            
            # Draw Jummah box moved to below Isha (was at top left)
            if idx == 4:
                jummah_box_x = x
                jummah_box_y = y + box_h + lower_row_offset
                jummah_box_h = lower_row_box_height
                self.jummah_box_y = jummah_box_y
                self.jummah_box_h = jummah_box_h
                is_jummah_current = (current_prayer == 'Jummah')
                jummah_shape_id = self.draw_khutbah_box(jummah_box_x, jummah_box_y, box_width, jummah_box_h, is_current=is_jummah_current)
                if jummah_shape_id:
                    self.prayer_box_shape_ids['Jummah'] = jummah_shape_id
                    self.prayer_box_bounds['Jummah'] = (jummah_box_x, jummah_box_y, box_width, jummah_box_h)
                
                # Check if there are changes within 2 days (including day of change)
                has_upcoming_changes = False
                eid_event = self.get_active_eid_salah_event()
                if eid_event:
                    has_upcoming_changes = True
                if self.upcoming_changes:
                    for prayer_key, info in self.upcoming_changes.items():
                        days_until = info.get('days_until', 0)
                        # Show yellow ribbon from 2 days before until midnight on day of change
                        if 0 <= days_until <= 2:
                            has_upcoming_changes = True
                            break

                if (not has_upcoming_changes) and self.dst_change_info:
                    dst_days_until = self.dst_change_info.get('days_until', 99)
                    if 0 <= dst_days_until <= 2:
                        has_upcoming_changes = True
                
                announcement_ribbon_height = self.us(86, 52)
                yellow_ribbon_height = self.us(70, 40)
                ribbon_gap = self.us(5, 3)
                announcement_ribbon_y = height - self.us(92, 56)

                # Draw yellow ribbon above the announcement ribbon if there are upcoming changes.
                if has_upcoming_changes:
                    yellow_ribbon_y = announcement_ribbon_y - yellow_ribbon_height - ribbon_gap
                    self.draw_upcoming_changes_ribbon(0, yellow_ribbon_y, width, yellow_ribbon_height)

                # Draw announcement ribbon only when announcements exist.
                if self.announcements:
                    self.draw_announcement_ribbon(0, announcement_ribbon_y, width, announcement_ribbon_height)
            
            x_offset += box_w + spacing

        # Draw standalone current time centered between Next Prayer and Jummah boxes
        if next_prayer_box_x is not None and jummah_box_x is not None:
            next_center_x = next_prayer_box_x + (box_width / 2)
            jummah_center_x = jummah_box_x + (box_width / 2)

            middle_gap_width = max(0, jummah_box_x - (next_prayer_box_x + box_width))
            self.next_prayer_max_panel_width = max(self.us(220, 130), middle_gap_width - self.us(18, 10))

            current_time_x = (next_center_x + jummah_center_x) / 2

            # Keep the input y as the desired date-row anchor (under translation).
            current_time_y = self.us(220, 145)

            self.draw_current_time_display(current_time_x, current_time_y, next_prayer_name_for_display)

        if self.show_weather and self.weather_data:
            self.draw_weather(width, height)

        # Draw logo after ribbons so it appears on top
        self.draw_top_right_logo(width, height)

        if self.is_eid_day(self.get_current_date()):
            self.canvas.delete('animated_eid')
            self.draw_eid_fireworks(width, height, animated=True, tags='animated_eid')
            self.draw_eid_balloons(width, height, animated=True, tags='animated_eid')
            self.canvas.tag_raise('animated_eid')

        self.draw_build_info(width, height)

    def draw_elegent_compact_prayer_table(self, width, height, prayers_data, prayers, current_prayer):
        """Draw one centered table: Salah | Athan | Iqamah for elegent theme."""
        palette = self.get_theme_palette()

        self.prayer_box_shape_ids = {}
        self.prayer_box_bounds = {}
        self.salah_name_specs = []
        self.salah_name_canvas_ids = []

        table_w = min(self.us(1540, 940), width - self.us(120, 50))
        table_h = self.us(610, 360)
        table_x = (width - table_w) / 2
        table_y = (height / 2) - (table_h / 2) + self.us(72, 34)

        self.draw_rounded_rectangle(
            table_x,
            table_y,
            table_w,
            table_h,
            self.us(34, 18),
            fill=palette['card_fill'],
            outline=palette['card_outline'],
            outline_width=self.us(3, 2)
        )

        header_h = self.us(86, 48)
        self.draw_rounded_rectangle(
            table_x + self.us(8, 4),
            table_y + self.us(8, 4),
            table_w - self.us(16, 8),
            header_h,
            self.us(26, 14),
            fill='#f3e3b8',
            outline='',
            outline_width=1
        )

        col_name_x = table_x + (table_w * 0.20)
        col_athan_x = table_x + (table_w * 0.58)
        col_iqamah_x = table_x + (table_w * 0.82)

        self.canvas.create_text(col_name_x, table_y + (header_h / 2) + self.us(8, 4), text='Salah', font=('Arial', self.fs(28, 14), 'bold'), fill=palette['title_text'])
        self.canvas.create_text(col_athan_x, table_y + (header_h / 2) + self.us(8, 4), text='Athan', font=('Arial', self.fs(28, 14), 'bold'), fill=palette['title_text'])
        self.canvas.create_text(col_iqamah_x, table_y + (header_h / 2) + self.us(8, 4), text='Iqamah', font=('Arial', self.fs(28, 14), 'bold'), fill=palette['title_text'])

        row_area_y = table_y + header_h + self.us(20, 10)
        row_h = (table_h - header_h - self.us(34, 18)) / len(prayers)

        divider_x1 = table_x + (table_w * 0.41)
        divider_x2 = table_x + (table_w * 0.70)
        self.canvas.create_line(divider_x1, row_area_y - self.us(12, 6), divider_x1, table_y + table_h - self.us(18, 10), fill=palette['card_outline'], width=self.us(2, 1))
        self.canvas.create_line(divider_x2, row_area_y - self.us(12, 6), divider_x2, table_y + table_h - self.us(18, 10), fill=palette['card_outline'], width=self.us(2, 1))

        for idx, (display_name, key, arabic) in enumerate(prayers):
            y1 = row_area_y + (idx * row_h)
            y2 = y1 + row_h
            is_current = (key == current_prayer)

            row_fill = palette['card_current_fill'] if is_current else palette['card_fill']
            row_outline = palette['card_current_outline'] if is_current else ''
            row_x = table_x + self.us(14, 7)
            row_w = table_w - self.us(28, 14)

            row_fill_id = self.draw_alpha_fill(
                row_x, y1, row_w, row_h,
                fill_color=row_fill,
                opacity_percent=self.prayer_box_opacity_percent,
                radius=0
            )
            outline_width = self.us(2, 1)
            row_shape_id = self.canvas.create_rectangle(
                row_x,
                y1,
                row_x + row_w,
                y2,
                fill='',
                outline=row_outline,
                width=outline_width
            )
            self.canvas.tag_lower(row_fill_id, row_shape_id)
            self.prayer_box_fill_ids[key] = row_fill_id
            self.prayer_box_fill_styles[key] = {
                'x': row_x,
                'y': y1,
                'width': row_w,
                'height': row_h,
                'radius': 0
            }
            self.prayer_box_shape_ids[key] = row_shape_id
            self.prayer_box_bounds[key] = (row_x, y1, row_w, row_h)

            athan_time = prayers_data.get(f'{key}Athan', '--')
            iqamah_time = prayers_data.get(f'{key}Iqama', '--')
            if key == 'Shrouq':
                athan_time, _ = self.resolve_sunrise_time(prayers_data)
                if athan_time != '--' and 'AM' not in athan_time and 'PM' not in athan_time:
                    athan_time = athan_time + ' AM'
                shrouq_plus = int(self.config.get('shrouqplus', 10))
                iqamah_time = f'+{shrouq_plus} MIN'
            if key == 'Jummah':
                athan_time = '1:30 PM'
                iqamah_time = 'All Year Long'
            if key == 'Fajr':
                if athan_time != '--' and 'AM' not in athan_time and 'PM' not in athan_time:
                    athan_time = athan_time + ' AM'
                if iqamah_time != '--' and 'AM' not in iqamah_time and 'PM' not in iqamah_time:
                    iqamah_time = iqamah_time + ' AM'

            self.draw_salah_name_transition_text(
                col_name_x,
                y1 + (row_h / 2),
                display_name,
                arabic,
                ('Arial', self.fs(30, 15), 'bold'),
                ('Arial', self.fs(30, 15), 'bold'),
                palette['title_text'],
                row_fill
            )
            self.draw_time_text_with_meridiem(col_athan_x, y1 + (row_h / 2), athan_time, main_size=self.fs(48, 26), suffix_size=self.fs(22, 12), color=palette['athan_text'])
            self.draw_time_text_with_meridiem(col_iqamah_x, y1 + (row_h / 2), iqamah_time, main_size=self.fs(48, 26), suffix_size=self.fs(22, 12), color=palette['iqamah_text'])

    def draw_elegent_v2_left_prayer_table(self, width, height, prayers_data, prayers, current_prayer):
        """Draw elegent_v2 as a boxed table on the left side: Prayer | Athan | Iqamah."""
        palette = self.get_theme_palette()
        ui_family = getattr(self, 'ui_font_family', 'Bahnschrift')
        is_friday = (self.get_current_date().weekday() == 4)
        next_prayer_name, next_athan = self.get_next_prayer(prayers_data)
        next_prayer_key = self.get_next_iqamah_prayer_key(prayers_data)
        if not next_prayer_key:
            next_prayer_key = 'Duhr' if (is_friday and next_prayer_name == 'Jummah') else next_prayer_name

        # When countdown is intentionally held on Shrouq, keep a visible Next badge
        # on the following prayer row instead of colliding with Current on Shrouq.
        if next_prayer_key == current_prayer:
            order = ['Fajr', 'Shrouq', 'Jummah', 'Duhr', 'Asr', 'Maghrib', 'Isha'] if is_friday else ['Fajr', 'Shrouq', 'Duhr', 'Asr', 'Maghrib', 'Isha']
            try:
                idx = order.index(current_prayer)
                next_prayer_key = order[(idx + 1) % len(order)]
            except Exception:
                pass

        self.prayer_box_shape_ids = {}
        self.prayer_box_bounds = {}
        self.salah_name_specs = []
        self.salah_name_canvas_ids = []
        active_takbeer_key = self._get_arafah_takbeer_active_key()

        left_panel_x = self.us(36, 18)
        left_panel_y = self.us(236, 150)
        left_panel_w = min(self.us(880, 550), max(self.us(590, 360), width * 0.50))

        cards_bottom_margin = self.us(170, 100)
        row_gap = 0
        header_font_size = self.fs(30, 16)
        row_name_font_size = self.fs(48, 27)
        row_time_main_size = self.fs(58, 33)
        row_time_suffix_size = self.fs(30, 17)
        header_h = header_font_size + self.us(24, 14)
        row_content_h = max(row_name_font_size, row_time_main_size)
        row_h = row_content_h + self.us(24, 12)
        min_required_h = header_h + row_gap + (row_h * len(prayers)) + (row_gap * (len(prayers) - 1))
        max_h = max(self.us(520, 320), height - left_panel_y - cards_bottom_margin)
        if min_required_h > max_h:
            # Keep text readable while ensuring the full table fits on shorter screens.
            shrink_ratio = max_h / min_required_h
            header_font_size = max(self.fs(24, 13), int(header_font_size * shrink_ratio))
            row_name_font_size = max(self.fs(36, 20), int(row_name_font_size * shrink_ratio))
            row_time_main_size = max(self.fs(44, 24), int(row_time_main_size * shrink_ratio))
            row_time_suffix_size = max(self.fs(22, 12), int(row_time_suffix_size * shrink_ratio))
            header_h = header_font_size + self.us(20, 12)
            row_content_h = max(row_name_font_size, row_time_main_size)
            row_h = row_content_h + self.us(10, 5)

        col1_x = left_panel_x + (left_panel_w * 0.21)
        col2_x = left_panel_x + (left_panel_w * 0.46)
        col3_x = left_panel_x + (left_panel_w * 0.84)

        header_shape_id = self.draw_rounded_rectangle(
            left_panel_x,
            left_panel_y,
            left_panel_w,
            header_h,
            self.us(18, 10),
            fill='',
            outline='',
            outline_width=0
        )
        header_fill_id = self.draw_alpha_fill(
            left_panel_x + self.us(2, 1),
            left_panel_y + self.us(2, 1),
            left_panel_w - self.us(4, 2),
            header_h - self.us(4, 2),
            fill_color=palette['card_fill'],
            opacity_percent=self.prayer_box_opacity_percent,
            radius=self.us(16, 9)
        )
        self.canvas.tag_lower(header_fill_id, header_shape_id)

        header_y = left_panel_y + (header_h / 2)
        self.draw_salah_name_transition_text(
            left_panel_x + self.us(20, 12),
            header_y,
            'Prayer',
            'الصلاة',
            (ui_family, header_font_size, 'bold'),
            (ui_family, header_font_size, 'bold'),
            palette['title_text'],
            '#f3e3b8',
            anchor='w'
        )
        self.draw_salah_name_transition_text(
            col2_x,
            header_y,
            'Athan',
            'الأذان',
            (ui_family, header_font_size, 'bold'),
            (ui_family, header_font_size, 'bold'),
            palette['title_text'],
            '#f3e3b8',
            anchor='center'
        )
        self.draw_salah_name_transition_text(
            col3_x,
            header_y,
            'Iqamah',
            'الإقامة',
            (ui_family, header_font_size, 'bold'),
            (ui_family, header_font_size, 'bold'),
            palette['title_text'],
            '#f3e3b8',
            anchor='center'
        )

        for idx, (display_name, key, arabic) in enumerate(prayers):
            is_current = (key == current_prayer)
            y = left_panel_y + header_h + row_gap + (idx * (row_h + row_gap))
            change_info = self.changing_prayers.get(key, {}) if key in self.changing_prayers else {}
            tomorrow_iqamah_overlay = (change_info.get('tomorrow_iqama') or '--').strip()
            has_change_overlay = bool(change_info and tomorrow_iqamah_overlay and tomorrow_iqamah_overlay != '--')
            active_change_overlay = has_change_overlay and bool(self.ribbon_visible)
            if has_change_overlay and key == 'Fajr' and 'AM' not in tomorrow_iqamah_overlay and 'PM' not in tomorrow_iqamah_overlay:
                tomorrow_iqamah_overlay = tomorrow_iqamah_overlay + ' AM'

            light_row_keys = {'Shrouq', 'Asr', 'Isha'}
            base_fill_color = palette.get('card_alt_fill', palette['card_fill']) if key in light_row_keys else palette['card_fill']
            fill_color = palette['card_current_fill'] if is_current else base_fill_color
            corner_radius = self.us(18, 10)

            shape_id = self.draw_rounded_rectangle(
                left_panel_x,
                y,
                left_panel_w,
                row_h,
                corner_radius,
                fill='',
                outline='',
                outline_width=0
            )

            fill_id = self.draw_alpha_fill(
                left_panel_x,
                y,
                left_panel_w,
                row_h,
                fill_color=fill_color,
                opacity_percent=self.prayer_box_opacity_percent,
                radius=corner_radius
            )
            self.canvas.tag_lower(fill_id, shape_id)

            badge_dx = self.us(18, 9)
            badge_dy = self.us(12, 6)

            if key == next_prayer_key and not active_change_overlay:
                badge_w = self.us(116, 66)
                badge_h = self.us(44, 26)
                badge_x = (left_panel_x + left_panel_w) - (badge_w / 2) + badge_dx
                badge_y = y - (badge_h / 2) + badge_dy
                self.draw_rounded_rectangle(
                    badge_x,
                    badge_y,
                    badge_w,
                    badge_h,
                    self.us(18, 10),
                    fill='#c62828',
                    outline='',
                    outline_width=0
                )
                self.canvas.create_text(
                    badge_x + (badge_w / 2),
                    badge_y + (badge_h / 2),
                    text='Next',
                    font=(ui_family, self.fs(30, 16), 'bold'),
                    fill='white'
                )

            self.prayer_box_shape_ids[key] = shape_id
            self.prayer_box_bounds[key] = (left_panel_x, y, left_panel_w, row_h)
            self.prayer_box_fill_ids[key] = fill_id
            self.prayer_box_fill_styles[key] = {
                'x': left_panel_x,
                'y': y,
                'width': left_panel_w,
                'height': row_h,
                'radius': corner_radius,
                'fill_color': fill_color
            }

            athan_time = prayers_data.get(f'{key}Athan', '--')
            iqamah_time = prayers_data.get(f'{key}Iqama', '--')
            if key == 'Shrouq':
                athan_time, _ = self.resolve_sunrise_time(prayers_data)
                if athan_time != '--' and 'AM' not in athan_time and 'PM' not in athan_time:
                    athan_time = athan_time + ' AM'
                shrouq_plus = int(self.config.get('shrouqplus', 10))
                iqamah_time = f'+{shrouq_plus} MIN'
            if key == 'Fajr':
                if athan_time != '--' and 'AM' not in athan_time and 'PM' not in athan_time:
                    athan_time = athan_time + ' AM'
                if iqamah_time != '--' and 'AM' not in iqamah_time and 'PM' not in iqamah_time:
                    iqamah_time = iqamah_time + ' AM'
            if key == 'Jummah':
                jummah_time_text = '1:30 PM'
                if self.jummah_time:
                    jummah_time_text = self.jummah_time.strftime('%I:%M %p').lstrip('0')
                athan_time = jummah_time_text
                iqamah_time = 'All Year Long'

            center_y = y + (row_h / 2)

            name_left_x = left_panel_x + self.us(20, 12)

            if active_change_overlay:
                ribbon_state = 'normal' if self.ribbon_visible else 'hidden'
                notice_x = left_panel_x + self.us(2, 1)
                notice_y = y + self.us(2, 1)
                notice_w = left_panel_w - self.us(4, 2)
                notice_h = row_h - self.us(4, 2)
                notice_bg = self.draw_alpha_fill(
                    notice_x,
                    notice_y,
                    notice_w,
                    notice_h,
                    fill_color='white',
                    opacity_percent=97,
                    radius=max(0, corner_radius - self.us(2, 1)),
                    outline_color='#d32f2f',
                    outline_width=self.us(3, 2)
                )
                self.canvas.itemconfigure(notice_bg, state=ribbon_state, tags=('prayer_change_ribbon', 'prayer_change_ribbon_bg'))

                overlay_center_x = left_panel_x + (left_panel_w / 2)
                overlay_center_y = y + (row_h / 2)
                show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))
                arabic_time_text = tomorrow_iqamah_overlay
                arabic_time_text = arabic_time_text.replace(' AM', ' صباحًا').replace(' PM', ' مساءً')
                arabic_time_text = arabic_time_text.replace(' am', ' صباحًا').replace(' pm', ' مساءً')
                if show_arabic_name:
                    full_overlay_text = self._prepare_canvas_rtl_text(
                        f"تتغيّر إقامة صلاة {arabic} إلى الساعة {arabic_time_text} غدًا"
                    )
                else:
                    prefix_text = f'{display_name} Iqamah changes to '
                    time_text = tomorrow_iqamah_overlay
                    suffix_text = ' Tomorrow'

                max_text_width = max(self.us(420, 220), notice_w - self.us(40, 20))
                max_text_height = max(self.us(78, 42), notice_h - self.us(22, 12))

                if show_arabic_name:
                    overlay_font_size = self.fs(52, 28)
                    min_overlay_font_size = self.fs(30, 16)
                    while True:
                        overlay_font = (ui_family, overlay_font_size, 'bold')
                        overlay_font_obj = tkfont.Font(font=overlay_font)
                        total_w = overlay_font_obj.measure(full_overlay_text)
                        total_h = overlay_font_obj.metrics('linespace')
                        if (total_w <= max_text_width and total_h <= max_text_height) or overlay_font_size <= min_overlay_font_size:
                            break
                        overlay_font_size -= 1

                    self.canvas.create_text(
                        overlay_center_x,
                        overlay_center_y,
                        text=full_overlay_text,
                        font=overlay_font,
                        fill='black',
                        anchor='center',
                        tags=('prayer_change_ribbon',),
                        state=ribbon_state
                    )
                else:
                    prefix_size = self.fs(48, 25)
                    time_size = self.fs(68, 35)
                    suffix_size = self.fs(56, 29)
                    min_prefix_size = self.fs(24, 13)
                    min_time_size = self.fs(34, 18)
                    min_suffix_size = self.fs(28, 15)

                    while True:
                        prefix_font = (ui_family, prefix_size, 'bold')
                        time_font = (ui_family, time_size, 'bold')
                        suffix_font = (ui_family, suffix_size, 'bold')

                        prefix_obj = tkfont.Font(font=prefix_font)
                        time_obj = tkfont.Font(font=time_font)
                        suffix_obj = tkfont.Font(font=suffix_font)

                        prefix_w = prefix_obj.measure(prefix_text)
                        time_w = time_obj.measure(time_text)
                        suffix_w = suffix_obj.measure(suffix_text)
                        total_w = prefix_w + time_w + suffix_w
                        total_h = max(prefix_obj.metrics('linespace'), time_obj.metrics('linespace'), suffix_obj.metrics('linespace'))

                        if (total_w <= max_text_width and total_h <= max_text_height) or (prefix_size <= min_prefix_size or time_size <= min_time_size or suffix_size <= min_suffix_size):
                            break

                        if total_w > max_text_width:
                            prefix_size -= 1
                            time_size -= 1
                            suffix_size -= 1
                        if total_h > max_text_height:
                            prefix_size -= 1
                            time_size -= 1
                            suffix_size -= 1

                    start_x = overlay_center_x - (total_w / 2)

                    self.canvas.create_text(
                        start_x,
                        overlay_center_y,
                        text=prefix_text,
                        font=prefix_font,
                        fill='black',
                        anchor='w',
                        tags=('prayer_change_ribbon',),
                        state=ribbon_state
                    )
                    self.canvas.create_text(
                        start_x + prefix_w,
                        overlay_center_y,
                        text=time_text,
                        font=time_font,
                        fill='#c62828',
                        anchor='w',
                        tags=('prayer_change_ribbon',),
                        state=ribbon_state
                    )
                    self.canvas.create_text(
                        start_x + prefix_w + time_w,
                        overlay_center_y,
                        text=suffix_text,
                        font=suffix_font,
                        fill='#2e7d32',
                        anchor='w',
                        tags=('prayer_change_ribbon',),
                        state=ribbon_state
                    )
            else:
                name_font_size = row_name_font_size
                athan_main_size = row_time_main_size + self.fs(6, 3)
                athan_suffix_size = row_time_suffix_size + self.fs(2, 1)
                iqamah_main_size = row_time_main_size + self.fs(6, 3)
                iqamah_suffix_size = row_time_suffix_size + self.fs(2, 1)
                row_title_color = '#1f1406' if is_current else palette['title_text']
                athan_color = '#2b1d0e' if is_current else palette['athan_text']
                iqamah_color = '#2b1d0e' if is_current else palette['iqamah_text']
                if (not is_current) and key in {'Shrouq', 'Asr', 'Isha'}:
                    row_title_color = '#111111'
                    athan_color = '#111111'
                    iqamah_color = '#111111'
                if key == 'Jummah':
                    iqamah_main_size = self.fs(28, 16)
                    iqamah_suffix_size = self.fs(16, 10)

                self.draw_salah_name_transition_text(
                    name_left_x,
                    center_y,
                    display_name,
                    arabic,
                    (ui_family, name_font_size, 'bold'),
                    (ui_family, name_font_size, 'bold'),
                    row_title_color,
                    fill_color,
                    anchor='w'
                )
                if key == 'Jummah' and not bool(getattr(self, 'salah_names_show_arabic', False)):
                    jummah_font = (ui_family, name_font_size, 'bold')
                    khutbah_font = (ui_family, self.fs(16, 9), 'bold')
                    jummah_width = tkfont.Font(font=jummah_font).measure('Jummah')
                    self.canvas.create_text(
                        name_left_x + jummah_width + self.us(14, 8),
                        center_y + self.us(1, 1),
                        text='Khutbah',
                        font=khutbah_font,
                        fill=row_title_color,
                        anchor='w'
                    )
                self.draw_time_text_with_meridiem(
                    col2_x - self.us(60, 34),
                    center_y,
                    athan_time,
                    main_size=athan_main_size,
                    suffix_size=athan_suffix_size,
                    color=athan_color,
                    anchor='w'
                )
                self.draw_time_text_with_meridiem(
                    col3_x,
                    center_y,
                    iqamah_time,
                    main_size=iqamah_main_size,
                    suffix_size=iqamah_suffix_size,
                    color=iqamah_color
                )

        self.next_prayer_athan_time = next_athan

        right_area_x1 = left_panel_x + left_panel_w + self.us(26, 16)
        right_area_w = max(self.us(320, 200), width - right_area_x1 - self.us(34, 18))
        right_center_x = right_area_x1 + (right_area_w / 2)

        self.next_prayer_max_panel_width = max(self.us(320, 200), right_area_w - self.us(20, 10))
        self.jummah_box_y = self.us(360, 240)
        self.jummah_box_h = self.us(250, 150)
        self.draw_current_time_display(right_center_x, self.us(170, 110), next_prayer_name)
        self.draw_arafah_takbeer_panel(right_area_x1, right_area_w)

        has_upcoming_changes = False
        eid_event = self.get_active_eid_salah_event()
        if eid_event:
            has_upcoming_changes = True
        if self.upcoming_changes:
            for prayer_key, info in self.upcoming_changes.items():
                days_until = info.get('days_until', 0)
                if 0 <= days_until <= 2:
                    has_upcoming_changes = True
                    break

        if (not has_upcoming_changes) and self.dst_change_info:
            dst_days_until = self.dst_change_info.get('days_until', 99)
            if 0 <= dst_days_until <= 2:
                has_upcoming_changes = True

        announcement_ribbon_height = self.us(86, 52)
        yellow_ribbon_height = self.us(70, 40)
        ribbon_gap = self.us(5, 3)
        announcement_ribbon_y = height - self.us(92, 56)

        if has_upcoming_changes:
            yellow_ribbon_y = announcement_ribbon_y - yellow_ribbon_height - ribbon_gap
            self.draw_upcoming_changes_ribbon(0, yellow_ribbon_y, width, yellow_ribbon_height)

        if self.announcements:
            self.draw_announcement_ribbon(0, announcement_ribbon_y, width, announcement_ribbon_height)

        # Keep Arafah hadith panel and text over all ribbons when panel is active.
        self.canvas.tag_raise('arafah_hadith_panel')
        self.canvas.tag_raise('arafah_hadith_text')

    def draw_salah_name_transition_text(self, x, y, english_text, arabic_text, english_font, arabic_font, fill_color, background_color, anchor='center', record_spec=True):
        """Draw a short slide/fade transition between English and Arabic salah names."""
        created_ids = []

        if record_spec:
            self.salah_name_specs.append({
                'x': x,
                'y': y,
                'english_text': english_text,
                'arabic_text': arabic_text,
                'english_font': english_font,
                'arabic_font': arabic_font,
                'fill_color': fill_color,
                'background_color': background_color,
                'anchor': anchor
            })

        def _draw_text(tx, ty, text, font, fill, anc):
            item_id = self.canvas.create_text(
                tx,
                ty,
                text=text,
                font=font,
                fill=fill,
                anchor=anc,
                tags=('salah_name_dynamic',)
            )
            created_ids.append(item_id)
            return item_id

        # Elegant modes use a softer crossfade (no travel/blink flash).
        theme_name = self.get_theme_name()
        if theme_name in ('elegent', 'elegent_v2'):
            transition_active, source_show_arabic, target_show_arabic, eased = self.get_salah_name_transition_state()
            show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))
            has_arabic_text = bool(arabic_text and str(arabic_text).strip())
            if not has_arabic_text:
                _draw_text(x, y, english_text, english_font, fill_color, anchor)
                if record_spec:
                    self.salah_name_canvas_ids.extend(created_ids)
                return created_ids

            if not transition_active:
                name_text = arabic_text if show_arabic_name else english_text
                name_font = arabic_font if show_arabic_name else english_font
                _draw_text(x, y, name_text, name_font, fill_color, anchor)
                if record_spec:
                    self.salah_name_canvas_ids.extend(created_ids)
                return created_ids

            outgoing_text = arabic_text if source_show_arabic else english_text
            outgoing_font = arabic_font if source_show_arabic else english_font
            incoming_text = arabic_text if target_show_arabic else english_text
            incoming_font = arabic_font if target_show_arabic else english_font

            # Fade via a darker shade only (no white/light flash during transition).
            dark_fade_color = self._mix_hex_color(fill_color, '#000000', 0.45)
            # Two-phase fade avoids overlapping both languages at once.
            if eased < 0.5:
                phase_t = eased / 0.5
                phase_fill = self._mix_hex_color(fill_color, dark_fade_color, phase_t)
                _draw_text(x, y, outgoing_text, outgoing_font, phase_fill, anchor)
            else:
                phase_t = (eased - 0.5) / 0.5
                phase_fill = self._mix_hex_color(dark_fade_color, fill_color, phase_t)
                _draw_text(x, y, incoming_text, incoming_font, phase_fill, anchor)
            if record_spec:
                self.salah_name_canvas_ids.extend(created_ids)
            return created_ids

        transition_active, source_show_arabic, target_show_arabic, eased = self.get_salah_name_transition_state()
        show_arabic_name = target_show_arabic if transition_active else bool(getattr(self, 'salah_names_show_arabic', False))
        has_arabic_text = bool(arabic_text and str(arabic_text).strip())

        if not has_arabic_text:
            _draw_text(x, y, english_text, english_font, fill_color, anchor)
            if record_spec:
                self.salah_name_canvas_ids.extend(created_ids)
            return created_ids

        if not transition_active:
            name_text = arabic_text if show_arabic_name else english_text
            name_font = arabic_font if show_arabic_name else english_font
            _draw_text(x, y, name_text, name_font, fill_color, anchor)
            if record_spec:
                self.salah_name_canvas_ids.extend(created_ids)
            return created_ids

        outgoing_text = arabic_text if source_show_arabic else english_text
        outgoing_font = arabic_font if source_show_arabic else english_font
        incoming_text = arabic_text if target_show_arabic else english_text
        incoming_font = arabic_font if target_show_arabic else english_font

        if outgoing_text == incoming_text and outgoing_font == incoming_font:
            _draw_text(x, y, incoming_text, incoming_font, fill_color, anchor)
            if record_spec:
                self.salah_name_canvas_ids.extend(created_ids)
            return created_ids

        travel = self.us(26, 12)
        outgoing_y = y - (travel * eased)
        incoming_y = y + (travel * (1.0 - eased))
        outgoing_fill = self._mix_hex_color(fill_color, background_color, min(1.0, eased * 0.9))
        incoming_fill = self._mix_hex_color(background_color, fill_color, eased)

        _draw_text(x, outgoing_y, outgoing_text, outgoing_font, outgoing_fill, anchor)
        _draw_text(x, incoming_y, incoming_text, incoming_font, incoming_fill, anchor)
        if record_spec:
            self.salah_name_canvas_ids.extend(created_ids)
        return created_ids

    def _redraw_salah_name_texts_only(self):
        """Redraw only prayer-name text items to avoid flickering full box redraws."""
        specs = list(getattr(self, 'salah_name_specs', []))
        if not specs:
            return False

        try:
            self.canvas.delete('salah_name_dynamic')
        except:
            pass

        for item_id in getattr(self, 'salah_name_canvas_ids', []):
            try:
                self.canvas.delete(item_id)
            except:
                pass
        self.salah_name_canvas_ids = []

        for spec in specs:
            self.draw_salah_name_transition_text(
                spec['x'],
                spec['y'],
                spec['english_text'],
                spec['arabic_text'],
                spec['english_font'],
                spec['arabic_font'],
                spec['fill_color'],
                spec['background_color'],
                anchor=spec.get('anchor', 'center'),
                record_spec=False
            )

        return True

    def get_salah_name_transition_state(self):
        """Return (active, source_show_arabic, target_show_arabic, eased_progress)."""
        current_show_arabic = bool(getattr(self, 'salah_names_show_arabic', False))
        if not getattr(self, 'salah_name_transition_active', False):
            return False, current_show_arabic, current_show_arabic, 1.0

        target_show_arabic = bool(getattr(self, 'salah_name_transition_target_arabic', current_show_arabic))
        source_show_arabic = not target_show_arabic
        progress = max(0.0, min(1.0, float(getattr(self, 'salah_name_transition_progress', 1.0))))
        eased = progress * progress * (3.0 - (2.0 * progress))
        return True, source_show_arabic, target_show_arabic, eased

    def _prepare_canvas_rtl_text(self, text):
        """Prepare Arabic text for Tk canvas rendering when bidi shaping is limited."""
        try:
            raw_text = str(text or '').replace('\u202B', '').replace('\u202C', '').strip()
            if not raw_text:
                return raw_text
            # If Arabic letters are present, reverse token order for visual RTL flow on Tk canvas.
            if re.search(r'[\u0600-\u06FF]', raw_text):
                parts = [part for part in raw_text.split(' ') if part]
                return ' '.join(reversed(parts))
            return raw_text
        except Exception:
            return str(text or '')
    
    def draw_prayer_box(self, x, y, width, height, name, arabic, athan, iqamah, is_current=False, show_tomorrow_iqamah=False, prayer_key=None, tomorrow_iqamah=None):
        """Draw a single prayer time box with rounded corners"""
        palette = self.get_theme_palette()
        theme_name = self.get_theme_name()
        # Different colors for current prayer
        if is_current:
            fill_color = palette['card_current_fill']
            outline_color = palette['card_current_outline']
            outline_w = 4
        else:
            fill_color = palette['card_fill']
            outline_color = palette['card_outline']
            outline_w = 3
        
        # Draw smooth alpha background with outline in same PIL image (no corner gaps)
        corner_radius = self.us(40, 22)
        fill_id = self.draw_alpha_fill(
            x, y, width, height,
            fill_color=fill_color,
            opacity_percent=self.prayer_box_opacity_percent,
            radius=corner_radius,
            outline_color=outline_color,
            outline_width=outline_w
        )
        box_shape_id = fill_id
        if prayer_key:
            self.prayer_box_fill_ids[prayer_key] = fill_id
            self.prayer_box_shape_ids[prayer_key] = fill_id
            self.prayer_box_fill_styles[prayer_key] = {
                'x': x,
                'y': y,
                'width': width,
                'height': height,
                'radius': corner_radius,
                'fill_color': fill_color
            }

        if theme_name == 'elegent':
            header_h = self.us(58, 28)
            self.draw_rounded_rectangle(
                x + self.us(6, 3), y + self.us(6, 3),
                width - self.us(12, 6), header_h,
                self.us(22, 12),
                fill='#f3e3b8',
                outline='',
                outline_width=1
            )
            self.canvas.create_line(
                x + self.us(18, 10), y + header_h + self.us(10, 5),
                x + width - self.us(18, 10), y + header_h + self.us(10, 5),
                fill=palette['card_outline'],
                width=self.us(2, 1)
            )
        
        # Rotating prayer name (English/Arabic)
        self.draw_salah_name_transition_text(
            x + width/2,
            y + self.us(42, 20),
            name,
            arabic,
            ('Arial', self.fs(42, 21), 'bold'),
            ('Arial', self.fs(42, 21), 'bold'),
            palette['title_text'],
            fill_color
        )
        
        if theme_name == 'elegent':
            label_y = y + self.us(100, 48)
            self.canvas.create_text(
                x + (width * 0.28), label_y,
                text='ATHAN',
                font=('Arial', self.fs(19, 9), 'bold'),
                fill=palette['subtle_text']
            )
            self.canvas.create_text(
                x + (width * 0.72), label_y,
                text='IQAMAH',
                font=('Arial', self.fs(19, 9), 'bold'),
                fill=palette['subtle_text']
            )
            self.canvas.create_line(
                x + (width / 2), y + self.us(118, 56),
                x + (width / 2), y + height - self.us(26, 12),
                fill=palette['card_outline'],
                width=self.us(2, 1)
            )

            time_y = y + self.us(155, 74)
            self.draw_time_text_with_meridiem(
                x + (width * 0.28), time_y,
                athan,
                main_size=self.fs(50, 24),
                suffix_size=self.fs(20, 10),
                color=palette['athan_text']
            )
            self.draw_time_text_with_meridiem(
                x + (width * 0.72), time_y,
                iqamah,
                main_size=self.fs(50, 24),
                suffix_size=self.fs(20, 10),
                color=palette['iqamah_text']
            )
        else:
            # Athan time
            athan_y = y + self.us(120, 56)
            self.draw_time_text_with_meridiem(
                x + width/2, athan_y,
                athan,
                main_size=self.fs(60, 30),
                suffix_size=self.fs(24, 12),
                color=palette['athan_text']
            )

            # Iqamah time
            iqamah_y = athan_y + self.us(72, 34)
            self.draw_time_text_with_meridiem(
                x + width/2, iqamah_y,
                iqamah,
                main_size=self.fs(60, 30),
                suffix_size=self.fs(24, 12),
                color=palette['iqamah_text']
            )

        # Draw full-box change notice if prayer changes tomorrow (1 day before change)
        if show_tomorrow_iqamah and tomorrow_iqamah:
            ribbon_state = 'normal' if self.ribbon_visible else 'hidden'

            notice_pad = self.us(4, 2)
            notice_x1 = x + notice_pad
            notice_y1 = y + notice_pad
            notice_w = width - notice_pad * 2
            notice_h = height - notice_pad * 2

            # Full notice background with rounded corners matching prayer box
            notice_bg = self.draw_alpha_fill(
                notice_x1, notice_y1, notice_w, notice_h,
                fill_color='white',
                opacity_percent=97,
                radius=corner_radius,
                outline_color='#ff0000',
                outline_width=self.us(3, 2)
            )
            self.canvas.itemconfigure(notice_bg, state=ribbon_state, tags=('prayer_change_ribbon', 'prayer_change_ribbon_bg'))

            center_x = x + (width / 2)
            main_time_text = (tomorrow_iqamah or '--').strip()
            suffix_time_text = ''
            split_time = main_time_text.rsplit(' ', 1)
            if len(split_time) == 2 and split_time[1].upper() in ('AM', 'PM', 'MIN'):
                main_time_text = split_time[0]
                suffix_time_text = f" {split_time[1].upper()}"

            # 3-line layout optimized for very large time visibility inside the prayer box.
            heading_text = name.upper()
            base_name_size = self.fs(82, 41)
            base_time_main_size = self.fs(178, 88)
            base_time_suffix_size = self.fs(72, 36)
            base_tomorrow_size = self.fs(56, 28)
            max_text_width = notice_w * 0.95
            max_text_height = notice_h * 0.95
            size_scale = 1.80

            name_size = base_name_size
            time_main_size = base_time_main_size
            time_suffix_size = base_time_suffix_size
            tomorrow_size = base_tomorrow_size
            name_h = time_h = tomorrow_h = 0
            gap = self.us(16, 8)

            while size_scale >= 0.95:
                name_size = max(self.fs(48, 24), int(round(base_name_size * size_scale)))
                time_main_size = max(self.fs(92, 48), int(round(base_time_main_size * size_scale)))
                time_suffix_size = max(self.fs(38, 19), int(round(base_time_suffix_size * size_scale)))
                tomorrow_size = max(self.fs(34, 17), int(round(base_tomorrow_size * size_scale)))

                name_font = (self.ui_font_family, name_size, 'bold')
                time_main_font = (self.ui_font_family, time_main_size, 'bold')
                time_suffix_font = (self.ui_font_family, time_suffix_size, 'bold')
                tomorrow_font = (self.ui_font_family, tomorrow_size, 'bold')

                name_font_obj = tkfont.Font(font=name_font)
                time_main_font_obj = tkfont.Font(font=time_main_font)
                time_suffix_font_obj = tkfont.Font(font=time_suffix_font)
                tomorrow_font_obj = tkfont.Font(font=tomorrow_font)

                name_w = name_font_obj.measure(heading_text)
                time_w = time_main_font_obj.measure(main_time_text)
                if suffix_time_text:
                    time_w += time_suffix_font_obj.measure(suffix_time_text)
                tomorrow_w = tomorrow_font_obj.measure('TOMORROW')
                max_line_width = max(name_w, time_w, tomorrow_w)

                name_h = name_font_obj.metrics('linespace')
                time_h = max(time_main_font_obj.metrics('linespace'), time_suffix_font_obj.metrics('linespace'))
                tomorrow_h = tomorrow_font_obj.metrics('linespace')
                gap = max(self.us(18, 9), int(round(time_h * 0.16)))
                total_h = name_h + time_h + tomorrow_h + (gap * 2)

                if max_line_width <= max_text_width and total_h <= max_text_height:
                    break

                size_scale -= 0.03

            total_h = name_h + time_h + tomorrow_h + (gap * 2)
            content_top_y = y + max(self.us(10, 5), (height - total_h) / 2)
            line1_y = content_top_y + (name_h / 2)
            line2_y = line1_y + (name_h / 2) + gap + (time_h / 2)
            line3_y = line2_y + (time_h / 2) + gap + (tomorrow_h / 2)

            # Line 1: Prayer name
            self.canvas.create_text(
                center_x, line1_y,
                text=heading_text,
                font=(self.ui_font_family, name_size, 'bold'),
                fill='black',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 2: New time with smaller AM/PM suffix (matching main prayer time style)
            self.draw_time_text_with_meridiem(
                center_x, line2_y,
                tomorrow_iqamah,
                main_size=time_main_size,
                suffix_size=time_suffix_size,
                color='#ff0000',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 3: Tomorrow
            self.canvas.create_text(
                center_x, line3_y,
                text='TOMORROW',
                font=(self.ui_font_family, tomorrow_size, 'bold'),
                fill='#ff0000',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )
        
        # Check for upcoming changes (3+ days ahead) - display as yellow news ribbon
        # This will be displayed separately in the main ribbon area, not in the prayer box
        # So we just remove this block completely from here
        return box_shape_id

    def update_prayer_box_highlight_states(self, current_prayer, blinking_prayer=None, blink_visible=True):
        """Update only prayer box highlight styles without full-canvas redraw."""
        palette = self.get_theme_palette()
        theme_name = self.get_theme_name()
        no_outline_mode = (theme_name == 'elegent_v2')
        for prayer_key, shape_id in self.prayer_box_shape_ids.items():
            try:
                row_style = self.prayer_box_fill_styles.get(prayer_key, {})
                row_base_fill = row_style.get('fill_color', palette['card_fill'])
                if prayer_key == blinking_prayer:
                    # Keep base box styling normal; foreground athan overlay handles flashing.
                    self.update_prayer_box_alpha_fill(
                        prayer_key,
                        palette['card_current_fill'],
                        '' if no_outline_mode else palette['card_current_outline'],
                        0 if no_outline_mode else 4
                    )
                elif prayer_key == current_prayer:
                    pass  # Glow animation handles current prayer
                else:
                    self.update_prayer_box_alpha_fill(
                        prayer_key,
                        row_base_fill,
                        '' if no_outline_mode else palette['card_outline'],
                        0 if no_outline_mode else 3
                    )
            except:
                pass
    
    def draw_rounded_rectangle(self, x, y, width, height, radius, **kwargs):
        """Draw a rectangle with rounded corners"""
        # Extract outline_width if provided and convert to width for polygon
        outline_width = kwargs.pop('outline_width', 1)
        
        points = [
            x + radius, y,
            x + width - radius, y,
            x + width, y,
            x + width, y + radius,
            x + width, y + height - radius,
            x + width, y + height,
            x + width - radius, y + height,
            x + radius, y + height,
            x, y + height,
            x, y + height - radius,
            x, y + radius,
            x, y,
        ]
        
        return self.canvas.create_polygon(
            points,
            smooth=True,
            width=outline_width,
            **kwargs
        )

    def _color_to_rgb(self, color):
        """Convert Tk color string to RGB tuple."""
        try:
            r16, g16, b16 = self.root.winfo_rgb(color)
            return (r16 // 256, g16 // 256, b16 // 256)
        except:
            return (255, 255, 255)

    def draw_alpha_fill(self, x, y, width, height, fill_color, opacity_percent, radius=0, tags=(), outline_color=None, outline_width=0):
        """Draw smooth alpha fill using an RGBA image, optionally with outline in the same image."""
        w = max(1, int(round(width)))
        h = max(1, int(round(height)))
        alpha = max(0, min(255, int(round((max(0, min(100, opacity_percent)) / 100.0) * 255))))
        r, g, b = self._color_to_rgb(fill_color)

        img = Image.new('RGBA', (w, h), (0, 0, 0, 0))
        draw = ImageDraw.Draw(img)
        rgba = (r, g, b, alpha)
        rad = max(1, int(round(radius))) if radius > 0 else 0

        if rad > 0:
            draw.rounded_rectangle((0, 0, w - 1, h - 1), radius=rad, fill=rgba)
        else:
            draw.rectangle((0, 0, w - 1, h - 1), fill=rgba)

        # Draw outline on the same image so fill and outline match perfectly
        if outline_color and outline_width > 0:
            or_, og, ob = self._color_to_rgb(outline_color)
            ow = max(1, int(round(outline_width)))
            outline_rgba = (or_, og, ob, 255)
            if rad > 0:
                draw.rounded_rectangle((0, 0, w - 1, h - 1), radius=rad, fill=None, outline=outline_rgba, width=ow)
            else:
                draw.rectangle((0, 0, w - 1, h - 1), fill=None, outline=outline_rgba, width=ow)

        photo = ImageTk.PhotoImage(img)
        image_id = self.canvas.create_image(int(round(x)), int(round(y)), image=photo, anchor='nw', tags=tags)
        self._alpha_image_refs[image_id] = photo
        return image_id

    def update_prayer_box_alpha_fill(self, prayer_key, fill_color, outline_color=None, outline_width=0, outline_alpha=255,
                                     animated_line=False, line_phase=0.0, line_color=None, override_alpha=None):
        """Update alpha fill+outline image in-place for a prayer box (no z-order change)."""
        style = self.prayer_box_fill_styles.get(prayer_key)
        if not style:
            return

        old_id = self.prayer_box_fill_ids.get(prayer_key)
        if not old_id:
            return

        w = max(1, int(round(style['width'])))
        h = max(1, int(round(style['height'])))
        if override_alpha is not None:
            alpha = max(0, min(255, int(override_alpha)))
        else:
            alpha = max(0, min(255, int(round((max(0, min(100, self.prayer_box_opacity_percent)) / 100.0) * 255))))
        r, g, b = self._color_to_rgb(fill_color)
        rad = max(1, int(round(style.get('radius', 0)))) if style.get('radius', 0) > 0 else 0

        img = Image.new('RGBA', (w, h), (0, 0, 0, 0))
        draw = ImageDraw.Draw(img)
        rgba = (r, g, b, alpha)

        if rad > 0:
            draw.rounded_rectangle((0, 0, w - 1, h - 1), radius=rad, fill=rgba)
        else:
            draw.rectangle((0, 0, w - 1, h - 1), fill=rgba)

        if outline_color and outline_width > 0:
            or_, og, ob = self._color_to_rgb(outline_color)
            ow = max(1, int(round(outline_width)))
            oa = max(0, min(255, int(outline_alpha)))
            outline_rgba = (or_, og, ob, oa)
            if rad > 0:
                draw.rounded_rectangle((0, 0, w - 1, h - 1), radius=rad, fill=None, outline=outline_rgba, width=ow)
            else:
                draw.rectangle((0, 0, w - 1, h - 1), fill=None, outline=outline_rgba, width=ow)

        # Optional traveling highlight segment around border.
        if animated_line:
            lw = max(4, int(round(outline_width)) * 3)
            seg_color = line_color or outline_color or '#ffffff'
            sr, sg, sb = self._color_to_rgb(seg_color)
            seg_rgba = (sr, sg, sb, 255)

            if rad > 0:
                # Rounded-rectangle perimeter path (clockwise), so the moving line hugs curved corners.
                rr = max(1, min(rad, (w - 1) // 2, (h - 1) // 2))
                top_len = max(0.0, float(w - 2 * rr - 1))
                side_len = max(0.0, float(h - 2 * rr - 1))
                arc_q = (math.pi * rr) / 2.0
                perim = max(1.0, (2.0 * top_len) + (2.0 * side_len) + (4.0 * arc_q))
                seg_len = max(12.0, perim * 0.22)
                start = (line_phase % 1.0) * perim

                cx_tr, cy_tr = (w - rr - 1), rr
                cx_br, cy_br = (w - rr - 1), (h - rr - 1)
                cx_bl, cy_bl = rr, (h - rr - 1)
                cx_tl, cy_tl = rr, rr

                def rounded_perimeter_point(dist):
                    d = dist % perim

                    if d <= top_len:
                        return (rr + d, 0)
                    d -= top_len

                    if d <= arc_q:
                        theta = (-math.pi / 2.0) + (d / rr)
                        return (cx_tr + (rr * math.cos(theta)), cy_tr + (rr * math.sin(theta)))
                    d -= arc_q

                    if d <= side_len:
                        return (w - 1, rr + d)
                    d -= side_len

                    if d <= arc_q:
                        theta = d / rr
                        return (cx_br + (rr * math.cos(theta)), cy_br + (rr * math.sin(theta)))
                    d -= arc_q

                    if d <= top_len:
                        return ((w - rr - 1) - d, h - 1)
                    d -= top_len

                    if d <= arc_q:
                        theta = (math.pi / 2.0) + (d / rr)
                        return (cx_bl + (rr * math.cos(theta)), cy_bl + (rr * math.sin(theta)))
                    d -= arc_q

                    if d <= side_len:
                        return (0, (h - rr - 1) - d)
                    d -= side_len

                    theta = math.pi + (d / rr)
                    return (cx_tl + (rr * math.cos(theta)), cy_tl + (rr * math.sin(theta)))

                pts = []
                step_px = 2.0
                sample_count = int(seg_len / step_px) + 1
                for i in range(sample_count + 1):
                    px, py = rounded_perimeter_point(start + (i * step_px))
                    pts.append((int(round(px)), int(round(py))))
                if len(pts) >= 2:
                    draw.line(pts, fill=seg_rgba, width=lw, joint='curve')
            else:
                # Non-rounded fallback.
                perim = max(4, (2 * (w + h) - 4))
                seg_len = max(10, int(perim * 0.22))
                start = int((line_phase % 1.0) * perim)

                def perimeter_point(dist):
                    d = dist % perim
                    if d < w:
                        return (d, 0)
                    d -= w
                    if d < h - 1:
                        return (w - 1, d + 1)
                    d -= (h - 1)
                    if d < w - 1:
                        return (w - 2 - d, h - 1)
                    d -= (w - 1)
                    return (0, h - 2 - d)

                pts = []
                step_px = 2
                for off in range(0, seg_len + 1, step_px):
                    pts.append(perimeter_point(start + off))
                if len(pts) >= 2:
                    draw.line(pts, fill=seg_rgba, width=lw, joint='curve')

        # Update the existing canvas image in-place (preserves z-order)
        new_photo = ImageTk.PhotoImage(img)
        try:
            self.canvas.itemconfig(old_id, image=new_photo)
        except:
            pass
        self._alpha_image_refs[old_id] = new_photo
    
    def draw_khutbah_box(self, x, y, width, height, is_current=False):
        """Draw Khutbah (Friday Sermon) box"""
        palette = self.get_theme_palette()
        text_y_offset = self.us(12, 6)
        # Draw rounded rectangle background with highlight if current
        if is_current:
            fill_color = palette['card_current_fill']
            outline_color = palette['card_current_outline']
            outline_w = 4
        else:
            fill_color = palette['card_fill']
            outline_color = palette['card_outline']
            outline_w = 3
        corner_radius = self.us(40, 22)
        fill_id = self.draw_alpha_fill(
            x, y, width, height,
            fill_color=fill_color,
            opacity_percent=self.prayer_box_opacity_percent,
            radius=corner_radius,
            outline_color=outline_color,
            outline_width=outline_w
        )
        box_shape_id = fill_id
        self.prayer_box_fill_ids['Jummah'] = fill_id
        self.prayer_box_shape_ids['Jummah'] = fill_id
        self.prayer_box_fill_styles['Jummah'] = {
            'x': x,
            'y': y,
            'width': width,
            'height': height,
            'radius': corner_radius,
            'fill_color': fill_color
        }
        
        # Rotate only the top prayer name (JUMMAH <-> العربية); keep KHUTBAH in English
        show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))
        if show_arabic_name:
            title_text = 'الجمعة'
            title_font = ('Arial', self.fs(42, 21), 'bold')
        else:
            title_text = 'JUMMAH'
            title_font = ('Arial', self.fs(42, 21), 'bold')
        self.canvas.create_text(
            x + width/2, y + self.us(20, 10) + text_y_offset,
            text=title_text,
            font=title_font,
            fill=palette['title_text']
        )

        # Translate KHUTBAH label when Arabic mode is active.
        khutbah_label = 'الخُطْبَة' if show_arabic_name else 'KHUTBAH'
        self.canvas.create_text(
            x + width/2, y + self.us(62, 30) + text_y_offset,
            text=khutbah_label,
            font=('Arial', self.fs(18, 10)),
            fill=palette['subtle_text']
        )
        
        # Draw time - use loaded Jummah time
        jummah_time_str = '1:30 PM'  # Default
        if self.jummah_time:
            jummah_time_str = self.jummah_time.strftime('%I:%M %p').lstrip('0')
        
        self.draw_time_text_with_meridiem(
            x + width/2, y + self.us(112, 52) + text_y_offset,
            jummah_time_str,
            main_size=self.fs(54, 26),
            suffix_size=self.fs(24, 12),
            color=palette['athan_text']
        )
        
        # Draw "ALL YEAR LONG" using the same color as iqamah text
        self.canvas.create_text(
            x + width/2, y + height - self.us(40, 20),
            text='ALL YEAR LONG',
            font=('Arial', self.fs(28, 14), 'bold'),
            fill=palette['iqamah_text']
        )
        
        return box_shape_id
    
    def draw_shouruq_box(self, x, y, width, height, sunrise_time, is_current=False):
        """Draw Shouruq (Sunrise) box"""
        palette = self.get_theme_palette()
        if is_current:
            fill_color = palette['card_current_fill']
            outline_color = palette['card_current_outline']
            outline_w = 4
        else:
            fill_color = palette['card_fill']
            outline_color = palette['card_outline']
            outline_w = 3

        # Draw smooth alpha background with outline in same PIL image
        corner_radius = self.us(40, 22)
        fill_id = self.draw_alpha_fill(
            x, y, width, height,
            fill_color=fill_color,
            opacity_percent=self.prayer_box_opacity_percent,
            radius=corner_radius,
            outline_color=outline_color,
            outline_width=outline_w
        )
        box_shape_id = fill_id
        self.prayer_box_fill_ids['Shrouq'] = fill_id
        self.prayer_box_shape_ids['Shrouq'] = fill_id
        self.prayer_box_fill_styles['Shrouq'] = {
            'x': x,
            'y': y,
            'width': width,
            'height': height,
            'radius': corner_radius,
            'fill_color': fill_color
        }
        
        # Rotating Shrouq name (English/Arabic)
        show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))
        if show_arabic_name:
            title_text = 'الشروق'
            title_font = ('Arial', self.fs(42, 21), 'bold')
        else:
            title_text = 'Shrouq'
            title_font = ('Arial', self.fs(42, 21), 'bold')
        self.canvas.create_text(
            x + width/2, y + self.us(42, 20),
            text=title_text,
            font=title_font,
            fill=palette['title_text']
        )
        
        # Draw sunrise time
        self.draw_time_text_with_meridiem(
            x + width/2, y + self.us(126, 60),
            sunrise_time,
            main_size=self.fs(60, 30),
            suffix_size=self.fs(24, 12),
            color=palette['athan_text']
        )

        # Configurable +minutes note at the bottom
        shrouq_plus_minutes = int(self.config.get('shrouqplus', 10))
        self.canvas.create_text(
            x + width/2, y + height - self.us(40, 20),
            text=f'+ {shrouq_plus_minutes} MINUTES',
            font=('Arial', self.fs(34, 18), 'bold'),
            fill=palette['shrouq_note_text']
        )

        return box_shape_id

    def draw_time_text_with_meridiem(self, x, y, time_text, main_size=36, suffix_size=20, color='#1a3a5f', **kwargs):
        """Draw time with bigger numeric part and smaller AM/PM suffix"""
        normalized_text = (time_text or '--').strip()
        ui_family = getattr(self, 'ui_font_family', 'Bahnschrift')
        anchor = kwargs.pop('anchor', 'center')
        parts = normalized_text.rsplit(' ', 1)

        if len(parts) == 2 and parts[1].upper() in ('AM', 'PM', 'MIN'):
            main_text = parts[0]
            suffix_text = f" {parts[1].upper()}"

            main_font = (ui_family, main_size, 'bold')
            suffix_font = (ui_family, suffix_size, 'bold')

            main_width = tkfont.Font(font=main_font).measure(main_text)
            suffix_width = tkfont.Font(font=suffix_font).measure(suffix_text)
            total_width = main_width + suffix_width
            if anchor == 'w':
                left_x = x
            elif anchor == 'e':
                left_x = x - total_width
            else:
                left_x = x - (total_width / 2)

            self.canvas.create_text(
                left_x, y,
                text=main_text,
                font=main_font,
                fill=color,
                anchor='w',
                **kwargs
            )
            self.canvas.create_text(
                left_x + main_width, y,
                text=suffix_text,
                font=suffix_font,
                fill=color,
                anchor='w',
                **kwargs
            )
        else:
            self.canvas.create_text(
                x, y,
                text=normalized_text,
                font=(ui_family, main_size, 'bold'),
                fill=color,
                anchor=anchor,
                **kwargs
            )
    
    def draw_next_prayer_box(self, x, y, width, height, prayer_name, athan_time):
        """Legacy placement anchor (visual next-prayer content is now standalone)"""
        # Keep anchor values for layout/reference; countdown is drawn in draw_current_time_display
        self.countdown_y = y + 62
        self.countdown_x = x + width/2

    def draw_current_time_display(self, x, y, next_prayer_name):
        """Draw standalone current time display with seconds and next prayer below"""
        palette = self.get_theme_palette()
        # Live time text (updated every second in update_countdown)
        current_time_text = self.get_current_time().strftime('%I:%M:%S %p')

        # y now represents the date-row anchor (under translation).
        date_block_y = y

        # White rounded box like prayer boxes for next prayer info
        panel_height = self.next_prayer_panel_height
        # Align panel top with the top of the Shrouq/Jummah lower row.
        panel_y1 = self.jummah_box_y + ((self.jummah_box_h - panel_height) / 2) + self.us(34, 18)
        line_center_y = panel_y1 + (panel_height / 2)

        # Move current time noticeably higher relative to the lower prayer row.
        current_time_y = self.jummah_box_y + self.us(14, 8)
        outline_step = self.us(4, 3)
        outline_offsets = [
            (-outline_step, -outline_step), (-outline_step, 0), (-outline_step, outline_step),
            (0, -outline_step), (0, outline_step),
            (outline_step, -outline_step), (outline_step, 0), (outline_step, outline_step)
        ]
        self.current_time_outline_ids = []
        for dx, dy in outline_offsets:
            outline_id = self.canvas.create_text(
                x + dx, current_time_y + dy,
                text=current_time_text,
                font=('Arial', self.fs(100, 49), 'bold'),
                fill='black'
            )
            self.current_time_outline_ids.append(outline_id)

        self.current_time_text_id = self.canvas.create_text(
            x, current_time_y,
            text=current_time_text,
            font=('Arial', self.fs(100, 49), 'bold'),
            fill='white'
        )

        # Next prayer line in one row with split colors
        prayers_data = self.get_today_prayers()
        live_display_data = self.get_next_line_display_data(prayers_data)
        if not self._np_initialized:
            self._np_rtl = bool(live_display_data.get('rtl', False))
            self._np_initialized = True

        # Keep draw source locked to committed ticker mode; update_countdown decides when to switch.
        display_data = self.get_next_line_display_data(prayers_data, force_show_arabic=self._np_rtl)
        prefix_text = display_data['prefix_text']
        name_text = display_data['name_text']
        in_text = display_data['in_text']
        countdown_text = display_data['countdown_text']
        rtl_mode = bool(display_data.get('rtl', False))

        # Check if ticker animation is active and override draw data + compute shift factor
        _np_anim_data, _np_shift_factor = self._np_get_draw_data()
        if _np_anim_data is not None:
            prefix_text  = _np_anim_data.get('prefix', prefix_text)
            name_text    = _np_anim_data.get('name', name_text)
            in_text      = _np_anim_data.get('in_', in_text)
            countdown_text = _np_anim_data.get('countdown', countdown_text)
            rtl_mode     = bool(_np_anim_data.get('rtl', rtl_mode))
        line_size = int(self.next_prayer_line_font.cget('size'))
        prefix_size = int(self.next_prayer_prefix_font.cget('size'))
        min_line_size = max(18, self.fs(28, 14))
        min_prefix_size = max(14, self.fs(22, 12))
        rtl_gap = max(6, self.fs(8, 4))

        while True:
            line_font_obj = tkfont.Font(family='Arial', size=line_size, weight='bold')
            prefix_font_obj = tkfont.Font(family='Arial', size=prefix_size, weight='bold')

            prefix_width = prefix_font_obj.measure(prefix_text)
            name_width = line_font_obj.measure(name_text)
            in_width = line_font_obj.measure(in_text)
            countdown_width = line_font_obj.measure('88:88:88')
            if rtl_mode:
                total_width = prefix_width + name_width + in_width + countdown_width + (rtl_gap * 3)
            else:
                total_width = prefix_width + name_width + in_width + countdown_width

            unconstrained_panel_width = max(260, total_width + (self.next_prayer_panel_padding_x * 2))
            max_panel_width = self.next_prayer_max_panel_width if self.next_prayer_max_panel_width else unconstrained_panel_width
            panel_width = min(unconstrained_panel_width, max_panel_width)
            max_text_width = max(120, panel_width - (self.next_prayer_panel_padding_x * 2))

            if total_width <= max_text_width or (line_size <= min_line_size and prefix_size <= min_prefix_size):
                break

            if line_size > min_line_size:
                line_size -= 1
            if prefix_size > min_prefix_size:
                prefix_size -= 1

        self.next_prayer_line_font.configure(size=line_size)
        self.next_prayer_prefix_font.configure(size=prefix_size)
        self.next_prayer_countdown_fixed_width = self.next_prayer_line_font.measure('88:88:88')

        line_font = ('Arial', line_size, 'bold')
        prefix_font = ('Arial', prefix_size, 'bold')
        panel_center_x = x + self.us(24, 12)
        panel_x1 = panel_center_x - (panel_width / 2)

        self.next_prayer_panel_id = self.draw_rounded_rectangle(
            panel_x1, panel_y1, panel_width, panel_height, self.next_prayer_panel_radius,
            fill=palette['next_panel_fill'], outline=palette['next_panel_outline'], outline_width=3
        )

        # Constrain ticker travel to inner panel padding so text never leaves the white box.
        available_shift = max(0.0, ((panel_width - total_width) / 2.0) - 2.0)
        max_shift = min(available_shift, float(self.us(24, 12)))
        shift_x = _np_shift_factor * max_shift

        left_x = panel_center_x - (total_width / 2) + shift_x

        self.next_prayer_line_x = panel_center_x
        self.next_prayer_line_y = line_center_y
        self.next_prayer_panel_width = panel_width
        self.next_prayer_panel_bounds = (panel_x1, panel_y1, panel_width, panel_height)
        self.next_prayer_static_width = panel_width
        self._next_prayer_last_text_parts = (prefix_text, name_text, in_text)
        self._next_prayer_last_widths = (prefix_width, name_width, in_width, countdown_width)
        if rtl_mode:
            right_x = panel_center_x + (total_width / 2) + shift_x
            self.next_prayer_prefix_text_id = self.canvas.create_text(
                right_x, line_center_y,
                text=prefix_text,
                font=prefix_font,
                fill=palette['next_prefix_text'],
                anchor='e'
            )
            self.next_prayer_name_text_id = self.canvas.create_text(
                right_x - prefix_width - rtl_gap, line_center_y,
                text=name_text,
                font=line_font,
                fill=palette['next_name_text'],
                anchor='e'
            )
            self.next_prayer_in_text_id = self.canvas.create_text(
                right_x - prefix_width - rtl_gap - name_width - rtl_gap, line_center_y,
                text=in_text,
                font=line_font,
                fill=palette['next_in_text'],
                anchor='e'
            )
            self.countdown_text_id = self.canvas.create_text(
                right_x - prefix_width - rtl_gap - name_width - rtl_gap - in_width - rtl_gap, line_center_y,
                text=countdown_text,
                font=line_font,
                fill=palette['next_countdown_text'],
                anchor='e'
            )
        else:
            self.next_prayer_prefix_text_id = self.canvas.create_text(
                left_x, line_center_y,
                text=prefix_text,
                font=prefix_font,
                fill=palette['next_prefix_text'],
                anchor='w'
            )
            self.next_prayer_name_text_id = self.canvas.create_text(
                left_x + prefix_width, line_center_y,
                text=name_text,
                font=line_font,
                fill=palette['next_name_text'],
                anchor='w'
            )
            self.next_prayer_in_text_id = self.canvas.create_text(
                left_x + prefix_width + name_width, line_center_y,
                text=in_text,
                font=line_font,
                fill=palette['next_in_text'],
                anchor='w'
            )
            self.countdown_text_id = self.canvas.create_text(
                left_x + prefix_width + name_width + in_width, line_center_y,
                text=countdown_text,
                font=line_font,
                fill=palette['next_countdown_text'],
                anchor='w'
            )

        # Date row now appears under the translation area.
        current_date = self.get_current_date()
        show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))

        english_day_text = current_date.strftime('%A')
        english_miladi_text = current_date.strftime('%B %d, %Y')
        arabic_weekdays = {
            0: 'الاثنين',
            1: 'الثلاثاء',
            2: 'الأربعاء',
            3: 'الخميس',
            4: 'الجمعة',
            5: 'السبت',
            6: 'الأحد'
        }
        arabic_months = {
            1: 'يناير', 2: 'فبراير', 3: 'مارس', 4: 'أبريل',
            5: 'مايو', 6: 'يونيو', 7: 'يوليو', 8: 'أغسطس',
            9: 'سبتمبر', 10: 'أكتوبر', 11: 'نوفمبر', 12: 'ديسمبر'
        }
        arabic_day_text = arabic_weekdays.get(current_date.weekday(), english_day_text)
        arabic_miladi_text = f"{current_date.day} {arabic_months.get(current_date.month, '')} {current_date.year}"

        day_text = arabic_day_text if show_arabic_name else english_day_text
        miladi_text = arabic_miladi_text if show_arabic_name else english_miladi_text
        if Gregorian:
            try:
                hijri = Gregorian(current_date.year, current_date.month, current_date.day).to_hijri()
                english_hijri_text = f"{hijri.day} {self.get_hijri_month_name(hijri.month)} {hijri.year}H"
                arabic_hijri_months = {
                    1: 'محرم', 2: 'صفر', 3: 'ربيع الأول', 4: 'ربيع الآخر',
                    5: 'جمادى الأولى', 6: 'جمادى الآخرة', 7: 'رجب', 8: 'شعبان',
                    9: 'رمضان', 10: 'شوال', 11: 'ذو القعدة', 12: 'ذو الحجة'
                }
                arabic_hijri_text = f"{hijri.day} {arabic_hijri_months.get(hijri.month, '')} {hijri.year}هـ"
                hijri_text = arabic_hijri_text if show_arabic_name else english_hijri_text
            except:
                hijri_text = 'التاريخ الهجري غير متاح' if show_arabic_name else 'Hijri date unavailable'
        else:
            hijri_text = 'التاريخ الهجري غير متاح' if show_arabic_name else 'Hijri date unavailable'

        date_font = ('Arial', self.fs(42, 24), 'bold') if show_arabic_name else ('Arial', self.fs(36, 20), 'bold')

        if self.get_theme_name() != 'elegent_v2':
            self.draw_outlined_text(
                x, date_block_y,
                text=f"{day_text} | {hijri_text} | {miladi_text}",
                font=date_font,
                fill='white',
                outline='black',
                outline_px=self.us(3, 2),
                anchor='n'
            )

    def _should_draw_arafah_takbeer_panel(self):
        """Return True when the dedicated Takbeer panel should be visible."""
        if self.get_theme_name() != 'elegent_v2':
            return False
        if not bool(getattr(self, 'show_arafah_takbeer_panel', True)):
            return False
        if not bool(getattr(self, 'show_takbeer_shower', True)):
            return False
        if bool(getattr(self, 'athan_callout_prayer', None)):
            return False
        if not self.is_arafah_takbeer_window(self.get_current_date()):
            return False
        return self._get_arafah_takbeer_active_key() is not None

    def draw_arafah_takbeer_panel(self, right_area_x1, right_area_w):
        """Draw a dedicated Takbeer panel below weather cards on elegent_v2."""
        return

        palette = self.get_theme_palette()
        width = max(1, self.canvas.winfo_width())
        height = max(1, self.canvas.winfo_height())

        # Match the Athan callout footprint on elegent_v2.
        panel_x = right_area_x1
        panel_y = self.us(236, 150)
        panel_w = right_area_w
        panel_h = max((height - panel_y) - self.us(10, 6), self.us(480, 300))
        panel_radius = self.us(40, 22)
        panel_tags = ('arafah_hadith_panel',)
        text_tags = ('arafah_hadith_text',)

        self.draw_alpha_fill(
            panel_x,
            panel_y,
            panel_w,
            panel_h,
            fill_color='#142846',
            opacity_percent=92,
            radius=panel_radius,
            tags=panel_tags,
            outline_color='',
            outline_width=0
        )

        arabic_text = (
            'قَالَ رَسُولُ اللَّهِ ﷺ:\n'
            'خَيْرُ الدُّعَاءِ دُعَاءُ يَوْمِ عَرَفَةَ، وَخَيْرُ مَا قُلْتُ أَنَا وَالنَّبِيُّونَ مِنْ قَبْلِي:\n'
            'لَا إِلَهَ إِلَّا اللَّهُ وَحْدَهُ لَا شَرِيكَ لَهُ، لَهُ الْمُلْكُ وَلَهُ الْحَمْدُ،\n'
            'وَهُوَ عَلَى كُلِّ شَيْءٍ قَدِيرٌ'
        )
        english_text = (
            'The Messenger of Allah ﷺ said:\n'
            '"The best supplication is the supplication on the Day of Arafah.\n'
            'And the best of what I and the prophets before me have said is:\n'
            'There is no god but Allah, alone, without partner. To Him belongs the dominion\n'
            'and all praise, and He is capable of all things."'
        )

        content_w = panel_w - self.us(52, 28)
        center_x = panel_x + (panel_w / 2)
        top_pad = self.us(30, 16)
        bottom_pad = self.us(26, 14)
        section_gap = self.us(22, 12)
        text_top = panel_y + top_pad
        text_bottom = panel_y + panel_h - bottom_pad
        usable_h = max(self.us(220, 130), text_bottom - text_top)
        arabic_region_h = usable_h * 0.58
        english_y = text_top + arabic_region_h + section_gap

        arabic_size = self.fs(44, 26)
        english_size = self.fs(30, 18)
        min_arabic_size = self.fs(28, 16)
        min_english_size = self.fs(18, 11)
        min_gap = self.us(8, 4)

        for _ in range(8):
            self.canvas.delete('arafah_hadith_text')

            arabic_id = self.draw_outlined_text(
                center_x,
                text_top,
                text=arabic_text,
                font=('Traditional Arabic', arabic_size, 'bold'),
                fill='#f8fbff',
                outline='#08172e',
                outline_px=self.us(2, 1),
                anchor='n',
                justify='center',
                tags=text_tags,
                width=content_w
            )
            english_id = self.draw_outlined_text(
                center_x,
                english_y,
                text=english_text,
                font=('Arial', english_size, 'bold'),
                fill='#eaf2ff',
                outline='#08172e',
                outline_px=self.us(2, 1),
                anchor='n',
                justify='center',
                tags=text_tags,
                width=content_w
            )

            arabic_bbox = self.canvas.bbox(arabic_id)
            english_bbox = self.canvas.bbox(english_id)
            if not arabic_bbox or not english_bbox:
                break

            overlap = arabic_bbox[3] + min_gap > english_bbox[1]
            english_overflow = english_bbox[3] > text_bottom
            if not overlap and not english_overflow:
                break

            if overlap and arabic_size > min_arabic_size:
                arabic_size = max(min_arabic_size, arabic_size - 2)
            if english_overflow and english_size > min_english_size:
                english_size = max(min_english_size, english_size - 1)

        # Keep hadith text above all panel artwork.
        self.canvas.tag_raise('arafah_hadith_text')

    def draw_build_info(self, width, height):
        """Draw app build date/time in the bottom-right corner."""
        palette = self.get_theme_palette()
        self.build_info_text_id = self.canvas.create_text(
            width - self.us(14, 8),
            height - self.us(20, 12),
            text=self.build_info_text,
            font=('Arial', self.fs(18, 10)),
            fill=palette['build_info_text'],
            anchor='se'
        )
    
    def schedule_prayer_time_toggle(self):
        """Schedule the prayer time toggle every 15 minutes"""
        self.update_prayer_time_toggle()

    def _start_salah_name_transition(self, target_show_arabic):
        """Start a short animated transition between English and Arabic prayer names."""
        target_show_arabic = bool(target_show_arabic)
        current_show_arabic = bool(getattr(self, 'salah_names_show_arabic', False))

        # Elegant themes should transition more slowly and smoothly.
        if self.get_theme_name() in ('elegent', 'elegent_v2'):
            self.salah_name_transition_duration_ms = 950
            self.salah_name_transition_tick_ms = 55
        else:
            self.salah_name_transition_duration_ms = 280
            self.salah_name_transition_tick_ms = 45

        if not self.salah_name_transition_active and target_show_arabic == current_show_arabic:
            self._last_salah_name_arabic_state = target_show_arabic
            return

        self.salah_name_transition_target_arabic = target_show_arabic

        if self.salah_name_transition_after_id is not None:
            try:
                self.root.after_cancel(self.salah_name_transition_after_id)
            except:
                pass
            self.salah_name_transition_after_id = None

        self.salah_name_transition_active = True
        self.salah_name_transition_progress = 0.0
        if not self.iqamah_overlay_visible:
            if self.get_theme_name() in ('elegent', 'elegent_v2') and self._redraw_salah_name_texts_only():
                pass
            else:
                self.redraw_full_display()
        self.salah_name_transition_after_id = self.root.after(
            self.salah_name_transition_tick_ms,
            self._tick_salah_name_transition
        )

    def _tick_salah_name_transition(self):
        """Advance Arabic reveal progress and request redraws."""
        step = self.salah_name_transition_tick_ms / max(1, self.salah_name_transition_duration_ms)
        self.salah_name_transition_progress = min(1.0, self.salah_name_transition_progress + step)

        if not self.iqamah_overlay_visible:
            if self.get_theme_name() in ('elegent', 'elegent_v2') and self._redraw_salah_name_texts_only():
                pass
            else:
                self.redraw_full_display()

        if self.salah_name_transition_progress >= 1.0:
            self._finish_salah_name_transition()
            return

        self.salah_name_transition_after_id = self.root.after(
            self.salah_name_transition_tick_ms,
            self._tick_salah_name_transition
        )

    def _finish_salah_name_transition(self):
        """Finalize transition state."""
        self.salah_name_transition_after_id = None
        self.salah_name_transition_active = False
        self.salah_name_transition_progress = 1.0
        self.salah_names_show_arabic = self.salah_name_transition_target_arabic
        self._last_salah_name_arabic_state = self.salah_names_show_arabic

        if not self.iqamah_overlay_visible:
            if self.get_theme_name() in ('elegent', 'elegent_v2') and self._redraw_salah_name_texts_only():
                pass
            else:
                self.redraw_full_display()

    def update_salah_name_rotation_state(self):
        """Show Arabic prayer names briefly on a configurable cadence, otherwise default to English."""
        try:
            change_every_seconds = int(self.config.get('arabicchangeevery', 30))
            change_every_seconds = max(1, change_every_seconds)
        except:
            change_every_seconds = 30

        try:
            arabic_duration_seconds = int(self.config.get('arabicnameduration', 10))
            arabic_duration_seconds = max(0, arabic_duration_seconds)
        except:
            arabic_duration_seconds = 5
        arabic_duration_seconds = min(arabic_duration_seconds, change_every_seconds)

        now_dt = datetime.combine(self.get_current_date(), self.get_current_time())
        seconds_into_cycle = int(now_dt.timestamp()) % change_every_seconds
        show_arabic = arabic_duration_seconds > 0 and seconds_into_cycle < arabic_duration_seconds

        if self._last_salah_name_arabic_state is None:
            self._last_salah_name_arabic_state = show_arabic
            self.salah_names_show_arabic = show_arabic
            return

        if self.salah_name_transition_active:
            return

        if show_arabic != self._last_salah_name_arabic_state:
            self._start_salah_name_transition(show_arabic)
    
    def update_prayer_time_toggle(self):
        """Toggle between today's and tomorrow's Iqamah times - DISABLED"""
        # This function is now disabled because we use automatic switching
        # based on whether the next prayer has started (more intuitive behavior)
        # The show_tomorrow_time values are now set in check_prayer_changes()
        
        try:
            # Still increment counter for compatibility
            self.tomorrow_time_toggle_counter += 1
        except Exception as e:
            self._log(f"ERROR in update_prayer_time_toggle: {e}")
        
        # Schedule next check (disabled behavior, keep low frequency)
        try:
            self.root.after(5000, self.update_prayer_time_toggle)
        except:
            pass
    
    def schedule_ribbon_cycle(self):
        """Schedule ribbon visibility cycle using configured ON/OFF seconds."""
        self.update_ribbon_cycle()

    def _clear_ribbon_transition_artifacts(self):
        """Remove temporary shine items used for ribbon transition."""
        for item_id in getattr(self, '_ribbon_transition_ids', []):
            try:
                self.canvas.delete(item_id)
            except:
                pass
        self._ribbon_transition_ids = []
        self._ribbon_transition_photo_refs = []

    def _resolve_ribbon_mask_colors(self, cx, cy):
        """Pick base prayer-box colors under a ribbon card near center point (cx, cy)."""
        palette = self.get_theme_palette()
        fill_color = palette['card_fill']
        outline_color = palette['card_outline']
        try:
            for prayer_key, style in self.prayer_box_fill_styles.items():
                sx = style.get('x', 0)
                sy = style.get('y', 0)
                sw = style.get('width', 0)
                sh = style.get('height', 0)
                if sx <= cx <= (sx + sw) and sy <= cy <= (sy + sh):
                    if prayer_key == self.last_rendered_current_prayer:
                        fill_color = palette['card_current_fill']
                        outline_color = palette['card_current_outline']
                    else:
                        fill_color = style.get('fill_color', palette['card_fill'])
                    break
        except:
            pass
        return fill_color, outline_color

    def _draw_ribbon_transition_shine(self, t):
        """Draw moving shine across each visible iqamah-change ribbon box at progress t (0..1)."""
        self._clear_ribbon_transition_artifacts()

        bg_items = self.canvas.find_withtag('prayer_change_ribbon_bg')
        if not bg_items:
            return

        for item_id in bg_items:
            try:
                bbox = self.canvas.bbox(item_id)
            except:
                bbox = None
            if not bbox:
                continue
            x1, y1, x2, y2 = bbox
            iw = max(1, int(x2 - x1))
            ih = max(1, int(y2 - y1))
            sweep_x = int(x1 + ((x2 - x1) * t))

            # Peel/wipe mask: keep part of alert covered so the prayer-time box underneath
            # appears behind the moving line. Direction depends on show vs hide target.
            cx = (x1 + x2) / 2
            cy = (y1 + y2) / 2
            mask_fill, _mask_outline = self._resolve_ribbon_mask_colors(cx, cy)
            if self._ribbon_transition_target_visible:
                # Transition to alert: behind line -> alert, ahead -> prayer time.
                mx1, mx2 = sweep_x, x2
            else:
                # Transition to prayer time: behind line -> prayer time, ahead -> alert.
                mx1, mx2 = x1, sweep_x
            if mx2 > mx1:
                mask_id = self.draw_alpha_fill(
                    mx1, y1, mx2 - mx1, ih,
                    fill_color=mask_fill,
                    opacity_percent=100,
                    radius=0,
                    outline_color=None,
                    outline_width=0
                )
                self._ribbon_transition_ids.append(mask_id)

            img = Image.new('RGBA', (iw, ih), (0, 0, 0, 0))
            d = ImageDraw.Draw(img)
            tilt = int(ih * 0.28)
            strip_half = int(iw * 0.14)
            strip_cx = int(t * (iw + tilt * 2)) - tilt
            steps = 18
            for step in range(steps):
                frac = step / (steps - 1)
                dist = abs(frac - 0.5) * 2
                alpha = int(190 * (1.0 - dist ** 1.4))
                off = int((frac - 0.5) * strip_half * 2)
                px0 = strip_cx + off - tilt
                px1 = strip_cx + off + max(2, int(iw * 0.018)) + tilt
                d.polygon([(px0, 0), (px1, 0), (px1 + tilt * 2, ih), (px0 + tilt * 2, ih)],
                          fill=(255, 245, 200, alpha))

            photo = ImageTk.PhotoImage(img)
            self._ribbon_transition_photo_refs.append(photo)
            shine_id = self.canvas.create_image(int(x1), int(y1), image=photo, anchor='nw')
            self._ribbon_transition_ids.append(shine_id)
            try:
                self.canvas.tag_raise(shine_id)
            except:
                pass

    def _tick_ribbon_transition(self):
        """Animate one short shine sweep for ribbon show/hide transitions."""
        if not getattr(self, '_ribbon_transition_running', False):
            return
        frames = 11
        step = getattr(self, '_ribbon_transition_step', 0)
        t = 1.0 if frames <= 1 else (step / (frames - 1))

        self._draw_ribbon_transition_shine(t)
        self._ribbon_transition_step = step + 1

        if self._ribbon_transition_step < frames:
            try:
                self.root.after(33, self._tick_ribbon_transition)
            except:
                self._ribbon_transition_running = False
                self._clear_ribbon_transition_artifacts()
        else:
            self._ribbon_transition_running = False
            self._clear_ribbon_transition_artifacts()
            final_state = 'normal' if self._ribbon_transition_target_visible else 'hidden'
            try:
                self.canvas.itemconfig('prayer_change_ribbon', state=final_state)
            except:
                pass

    def _start_ribbon_transition(self, target_visible):
        """Start shine transition for iqamah-change ribbon show/hide."""
        # Never animate/show ribbon while iqamah overlay is active.
        if self.iqamah_overlay_visible:
            try:
                self.canvas.itemconfig('prayer_change_ribbon', state='hidden')
            except:
                pass
            self._ribbon_transition_running = False
            self._clear_ribbon_transition_artifacts()
            return

        self._ribbon_transition_running = False
        self._clear_ribbon_transition_artifacts()

        # Keep ribbon visible during animation so the sweep is seen.
        try:
            self.canvas.itemconfig('prayer_change_ribbon', state='normal')
        except:
            pass

        self._ribbon_transition_target_visible = bool(target_visible)
        self._ribbon_transition_step = 0
        self._ribbon_transition_running = True
        self._tick_ribbon_transition()
    
    def update_ribbon_cycle(self):
        """Update prayer-change ribbon visibility using configured ON/OFF seconds."""
        try:
            if self.iqamah_overlay_visible:
                # Keep ribbon hidden while overlay is visible.
                if self._ribbon_transition_running:
                    self._ribbon_transition_running = False
                    self._clear_ribbon_transition_artifacts()
                try:
                    self.canvas.itemconfig('prayer_change_ribbon', state='hidden')
                except:
                    pass
            else:
                prev_visible = self.ribbon_visible
                show_seconds = max(1, int(getattr(self, 'red_ribbon_show_seconds', self.config.get('redribbonshow', 15))))
                hide_seconds = max(1, int(getattr(self, 'red_ribbon_hide_seconds', self.config.get('redribbonhide', 45))))
                cycle_total = max(2, show_seconds + hide_seconds)
                self.ribbon_cycle_counter = (self.ribbon_cycle_counter + 1) % cycle_total
                self.ribbon_visible = (self.ribbon_cycle_counter < show_seconds)
                if self.ribbon_visible != prev_visible:
                    if self._ribbon_transition_running:
                        self._ribbon_transition_running = False
                        self._clear_ribbon_transition_artifacts()
                    state = 'normal' if self.ribbon_visible else 'hidden'
                    self.canvas.itemconfig('prayer_change_ribbon', state=state)
                    self.redraw_full_display()
                elif not self._ribbon_transition_running:
                    state = 'normal' if self.ribbon_visible else 'hidden'
                    self.canvas.itemconfig('prayer_change_ribbon', state=state)
        except Exception as e:
            self._log(f"ERROR in update_ribbon_cycle: {e}")
        
        # Schedule next update in 1 second
        try:
            self.root.after(1000, self.update_ribbon_cycle)
        except:
            pass
    
    def schedule_csv_reload(self):
        """Schedule CSV reload every 60 seconds"""
        self.update_csv_reload()
    
    def update_csv_reload(self):
        """Reload prayer times from CSV to catch any updates"""
        try:
            # Reload the CSV file
            self.load_prayer_times()
            self.load_announcements()
            
            # Recheck for changes (upcoming first, then tomorrow's)
            self.check_upcoming_changes()
            self.check_prayer_changes()

            # Refresh visible ribbons/content to reflect latest file changes
            if not self.iqamah_overlay_visible:
                self.redraw_full_display()
            
            self._log("CSV reloaded - prayer/announcement data updated")
        except Exception as e:
            self._log(f"ERROR in update_csv_reload: {e}")
        
        # Schedule next reload in 60 seconds (60000ms)
        try:
            self.root.after(60000, self.update_csv_reload)
        except:
            pass
    
    def draw_upcoming_changes_ribbon(self, x, y, width, height):
        """Draw a yellow news ribbon for upcoming prayer time changes"""
        # Skip drawing if yellow ribbon is in hidden phase
        if self.yellow_ribbon_hidden:
            return
        # Store ribbon position for animation updates
        self.yellow_ribbon_x = x
        self.yellow_ribbon_y = y
        self.yellow_ribbon_width = width
        self.yellow_ribbon_height = height
        
        # Draw yellow rectangle background
        self.canvas.create_rectangle(
            x, y, x + width, y + height,
            fill='#ffffcc',  # Yellow
            outline='#ffcc00',  # Gold border
            width=self.us(2, 1)
        )
        
        # Reset text IDs for this redraw
        self.yellow_ribbon_text_ids = []
        self.yellow_ribbon_x_positions = []
        current_x = width  # Start off-screen to the right, like announcement ticker
        
        # Build list of all upcoming changes
        # Yellow ribbon shows from 2 days before until midnight on day of change
        # days_until = 0 means changes today (at midnight) -> YELLOW RIBBON
        # days_until = 1 means changes tomorrow -> RED RIBBON + YELLOW RIBBON
        # days_until = 2 means changes in 2 days -> YELLOW RIBBON only
        changes_text = []
        eid_event = self.get_active_eid_salah_event()

        if eid_event:
            salah_dt = eid_event['salah_dt']
            eid_time = salah_dt.strftime('%I:%M %p').lstrip('0')
            eid_date = salah_dt.strftime('%a, %b %d %Y')

            arabic_weekdays = {
                'Monday': 'الاثنين',
                'Tuesday': 'الثلاثاء',
                'Wednesday': 'الأربعاء',
                'Thursday': 'الخميس',
                'Friday': 'الجمعة',
                'Saturday': 'السبت',
                'Sunday': 'الأحد'
            }
            arabic_months = {
                'January': 'يناير',
                'February': 'فبراير',
                'March': 'مارس',
                'April': 'أبريل',
                'May': 'مايو',
                'June': 'يونيو',
                'July': 'يوليو',
                'August': 'أغسطس',
                'September': 'سبتمبر',
                'October': 'أكتوبر',
                'November': 'نوفمبر',
                'December': 'ديسمبر'
            }
            arabic_period = 'صباحًا' if salah_dt.strftime('%p') == 'AM' else 'مساءً'
            arabic_time = f"{salah_dt.strftime('%I').lstrip('0') or '12'}:{salah_dt.strftime('%M')}"
            arabic_day = arabic_weekdays.get(salah_dt.strftime('%A'), salah_dt.strftime('%A'))
            arabic_month = arabic_months.get(salah_dt.strftime('%B'), salah_dt.strftime('%B'))
            arabic_time_token = f"{arabic_time} {arabic_period}"
            eid_label = str(eid_event.get('label', '') or '')
            takbeerat_match = re.search(r'takbeerat\s+starts\s+at\s+(\d{1,2}:\d{2}\s*[APap][Mm])', eid_label, re.IGNORECASE)
            takbeerat_time_token = None
            if takbeerat_match:
                takbeerat_time_str = re.sub(r'\s+', ' ', takbeerat_match.group(1).upper()).strip()
                try:
                    takbeerat_dt = datetime.strptime(takbeerat_time_str, '%I:%M %p')
                    takbeerat_period = 'صباحًا' if takbeerat_dt.strftime('%p') == 'AM' else 'مساءً'
                    takbeerat_time = f"{takbeerat_dt.strftime('%I').lstrip('0') or '12'}:{takbeerat_dt.strftime('%M')}"
                    takbeerat_time_token = f"{takbeerat_time} {takbeerat_period}"
                except Exception:
                    takbeerat_time_token = None
            if 'Fitr' in eid_label:
                eid_arabic_label = 'صلاة عيد الفطر'
            elif 'Adha' in eid_label:
                eid_arabic_label = 'صلاة عيد الأضحى'
            else:
                eid_arabic_label = 'صلاة العيد'
            if self.eid_ribbon_phase == 'arabic':
                # Arabic pass: left-to-right
                self.eid_ribbon_direction = 1
                changes_text.append({
                    # Single Arabic segment keeps word order stable across font/render changes.
                    'prefix': '',
                    'new_time': '',
                    'suffix': (
                        f"\u202Bتكبيرات عيد الأضحى تبدأ الساعة {takbeerat_time_token}، وصلاة العيد ستكون الساعة {arabic_time_token} يوم {arabic_day} {salah_dt.day} {arabic_month} {salah_dt.year}\u202C"
                        if ('Adha' in eid_label and takbeerat_time_token)
                        else f"\u202B{eid_arabic_label} ستكون الساعة {arabic_time_token} يوم {arabic_day} {salah_dt.day} {arabic_month} {salah_dt.year}\u202C"
                    ),
                    'prefix_color': 'black',
                    'new_time_color': 'black',
                    'suffix_color': 'black'
                })
            else:
                # English pass: right-to-left
                self.eid_ribbon_phase = 'english'
                self.eid_ribbon_direction = -1
                english_message = str(eid_event.get('message', '') or '').strip()
                if not english_message:
                    english_message = f"{eid_event['label']} at {eid_time} on {eid_date}"

                english_prefix = ''
                english_highlight = ''
                english_suffix = english_message
                time_match = re.search(re.escape(eid_time), english_message, re.IGNORECASE)
                if time_match:
                    english_prefix = english_message[:time_match.start()]
                    english_highlight = english_message[time_match.start():time_match.end()]
                    english_suffix = english_message[time_match.end():]

                changes_text.append({
                    'prefix': english_prefix,
                    'new_time': english_highlight,
                    'suffix': english_suffix,
                    'prefix_color': 'black',
                    'new_time_color': '#d32f2f',
                    'suffix_color': 'black'
                })

            # Repeated bilingual watermark pattern behind scrolling text.
            watermark_step = self.us(420, 240)
            pair_offset = self.us(230, 130)
            row_y_positions = [y + (height * 0.32), y + (height * 0.68)]
            for row_index, row_y in enumerate(row_y_positions):
                start_x = x + (watermark_step / 2)
                if row_index % 2 == 1:
                    start_x += watermark_step / 2
                current_wm_x = start_x
                while current_wm_x < (x + width):
                    self.canvas.create_text(
                        current_wm_x,
                        row_y,
                        text='EID MUBARAK',
                        font=('Arial', self.fs(24, 10), 'bold'),
                        fill='#f5e788'
                    )
                    self.canvas.create_text(
                        current_wm_x + pair_offset,
                        row_y,
                        text='عيد مبارك',
                        font=('Arial', self.fs(24, 10), 'bold'),
                        fill='#f5e788'
                    )
                    current_wm_x += watermark_step

        if self.upcoming_changes:
            for prayer_key, info in self.upcoming_changes.items():
                days_until = info.get('days_until', 0)
                # Yellow ribbon: show changes within 2 days (including day of change)
                if 0 <= days_until <= 2:
                    # prayer_key is already capitalized (e.g., 'Isha', 'Fajr')
                    prayer_name = prayer_key
                    change_date_str = info['change_date'].strftime('%a, %b %d')
                    old_time = info['old_time']
                    new_time = info['new_time']
                    
                    # Add AM to Fajr times if not already present
                    if prayer_key == 'Fajr':
                        if old_time != '--' and 'AM' not in old_time and 'PM' not in old_time:
                            old_time = old_time + ' AM'
                        if new_time != '--' and 'AM' not in new_time and 'PM' not in new_time:
                            new_time = new_time + ' AM'
                    
                    # Keep new time separate so it can be highlighted in red
                    changes_text.append({
                        'prefix': f"{prayer_name} iqamah time changes from {old_time} to ",
                        'new_time': new_time,
                        'suffix': f" on {change_date_str}"
                    })

        if self.dst_change_info:
            dst_days_until = self.dst_change_info.get('days_until', 99)
            if 0 <= dst_days_until <= 2:
                change_date = self.dst_change_info.get('change_date')
                shift_minutes = self.dst_change_info.get('shift_minutes', 0)
                direction_text = '1 HOUR AHEAD' if shift_minutes > 0 else '1 HOUR BEHIND'
                change_date_str = change_date.strftime('%a, %b %d') if change_date else ''

                changes_text.append({
                    'prefix': "Daylight Saving Time alert: all prayer times move ",
                    'new_time': direction_text,
                    'suffix': f" on {change_date_str}"
                })
        
        # If there are changes, display them with scrolling animation
        if changes_text:
            # Create text objects for each change with separators
            for i, change_item in enumerate(changes_text):
                segments = [
                    (change_item['prefix'], change_item.get('prefix_color', 'black')),
                    (change_item['new_time'], change_item.get('new_time_color', '#d32f2f')),
                    (change_item['suffix'], change_item.get('suffix_color', 'black'))
                ]

                for segment_text, segment_color in segments:
                    if not segment_text:
                        continue
                    ribbon_font = ('Arial', self.fs(40, 14), 'bold')
                    text_id = self.canvas.create_text(
                        x + current_x, y + height/2,
                        text=segment_text,
                        font=ribbon_font,
                        fill=segment_color,
                        anchor='w'
                    )
                    bbox = self.canvas.bbox(text_id)
                    text_width = bbox[2] - bbox[0] if bbox else len(segment_text) * 8

                    self.yellow_ribbon_text_ids.append((text_id, segment_text, segment_color, text_width))
                    self.yellow_ribbon_x_positions.append(current_x)
                    current_x += text_width

                current_x += self.us(30, 10)  # Add spacing after each full message
                
                # Add separator if not the last item
                if i < len(changes_text) - 1:
                    sep_text = "  ◆  "  # Diamond separator with spaces
                    sep_id = self.canvas.create_text(
                        x + current_x, y + height/2,
                        text=sep_text,
                        font=('Arial', self.fs(40, 14), 'bold'),
                        fill='black',
                        anchor='w'
                    )
                    # Calculate actual width for separator
                    sep_bbox = self.canvas.bbox(sep_id)
                    sep_width = sep_bbox[2] - sep_bbox[0] if sep_bbox else self.us(50, 20)
                    
                    self.yellow_ribbon_text_ids.append((sep_id, sep_text, 'black', sep_width))
                    self.yellow_ribbon_x_positions.append(current_x)
                    current_x += sep_width + self.us(10, 4)
            
            # Calculate total width for looping (same approach as announcement ticker)
            self.yellow_ribbon_total_width = 0
            if self.yellow_ribbon_text_ids and self.yellow_ribbon_x_positions:
                max_end = 0
                for idx, item in enumerate(self.yellow_ribbon_text_ids):
                    if idx < len(self.yellow_ribbon_x_positions):
                        end_x = self.yellow_ribbon_x_positions[idx] + item[3]
                        if end_x > max_end:
                            max_end = end_x
                self.yellow_ribbon_total_width = max_end + self.us(80, 24)

            # Keep existing scroll offset so redraws don't visibly restart the ticker.
            if not hasattr(self, 'yellow_ribbon_x_pos'):
                self.yellow_ribbon_x_pos = 0

            # For Eid language phases, initialize entry side per direction.
            if eid_event and self.yellow_ribbon_x_pos == 0:
                if self.eid_ribbon_direction > 0:
                    self.yellow_ribbon_x_pos = -self.yellow_ribbon_total_width
                else:
                    # Start just off-screen right so text appears quickly after ribbon shows.
                    self.yellow_ribbon_x_pos = 0

            # Immediately position text at current scroll offset to avoid flicker on redraw
            if self.yellow_ribbon_x_pos != 0:
                for i, (text_id, text, color, w) in enumerate(self.yellow_ribbon_text_ids):
                    if i < len(self.yellow_ribbon_x_positions):
                        x_offset = self.yellow_ribbon_x_pos + self.yellow_ribbon_x_positions[i]
                        self.canvas.coords(text_id, int(self.yellow_ribbon_x + x_offset), int(self.yellow_ribbon_y + self.yellow_ribbon_height / 2))
        # Note: If no changes, the yellow ribbon won't be drawn at all
    
    def draw_announcement_ribbon(self, x, y, width, height):
        """Draw announcement ribbon for news ticker with all announcements"""
        # Skip drawing if news tape is in hidden phase
        if self.news_tape_hidden:
            return
        # Draw dark navy rectangle background
        self.canvas.create_rectangle(
            x, y, x + width, y + height,
            fill=self.announcement_bg_color,
            outline='#162040',
            width=self.us(2, 1)
        )
        
        # Store ribbon info for updating
        self.ribbon_x = x
        self.ribbon_y = y
        self.ribbon_width = width
        self.ribbon_height = height
        
        # Create text objects for all announcements with their colors
        self.announcement_text_ids = []  # List of tuples: (text_id, text, color, width_estimate)
        self.announcement_x_positions = []  # Store starting x position of each item
        
        if self.announcements:
            # Start position (far right, outside visible area)
            current_x = width
            
            # Create text object for each announcement with its color
            for idx, (text, color) in enumerate(self.announcements):
                # Add separator before each announcement (except first)
                if idx > 0:
                    separator = "  *  "
                    sep_id = self.canvas.create_text(
                        int(x + current_x), int(y + height/2),
                        text=separator,
                        font=('Arial', self.fs(52, 18), 'bold'),
                        fill='#ffffff',
                        anchor='w'
                    )
                    # Get actual width from bounding box
                    bbox = self.canvas.bbox(sep_id)
                    sep_width = bbox[2] - bbox[0] if bbox else len(separator) * 12
                    self.announcement_text_ids.append((sep_id, separator, '#ffffff', sep_width))
                    self.announcement_x_positions.append(current_x)
                    current_x += sep_width + self.us(40, 12)  # Add gap after separator
                
                # Add the announcement
                text_id = self.canvas.create_text(
                    int(x + current_x), int(y + height/2),
                    text=text,
                    font=('Arial', self.fs(52, 18), 'bold'),
                    fill=color,
                    anchor='w'
                )
                # Get actual width from bounding box
                bbox = self.canvas.bbox(text_id)
                text_width = bbox[2] - bbox[0] if bbox else len(text) * 12
                self.announcement_text_ids.append((text_id, text, color, text_width))
                self.announcement_x_positions.append(current_x)
                # Add significant spacing after each announcement
                current_x += text_width + self.us(80, 24)
                
            self._log(f"Created {len(self.announcement_text_ids)} announcement text objects")
            # Debug output disabled to avoid Unicode encoding issues
            # for i, (tid, text, color, width) in enumerate(self.announcement_text_ids):
            #     print(f"  Item {i}: '{text}' width={width}")
        else:
            # Fallback if no announcements
            text_id = self.canvas.create_text(
                int(x + width), int(y + height/2),
                text="Welcome to Rose City Islamic Centre",
                font=('Arial', self.fs(52, 18), 'bold'),
                fill='white',
                anchor='w'
            )
            bbox = self.canvas.bbox(text_id)
            text_width = bbox[2] - bbox[0] if bbox else 400
            self.announcement_text_ids = [(text_id, "Welcome to Rose City Islamic Centre", 'white', text_width)]
            self.announcement_x_positions = [width]
        
        # Calculate total width
        self.announcement_total_width = (width - self.announcement_x_positions[0] if self.announcement_x_positions else 0)
        if self.announcement_text_ids:
            last_item = self.announcement_text_ids[-1]
            self.announcement_total_width = self.announcement_x_positions[-1] + last_item[3] + 80

        # Immediately position text at current scroll offset to avoid flicker on redraw
        if self.announcement_x_pos != 0:
            for i, (text_id, text, color, w) in enumerate(self.announcement_text_ids):
                if i < len(self.announcement_x_positions):
                    x_offset = self.announcement_x_pos + self.announcement_x_positions[i]
                    self.canvas.coords(text_id, int(self.ribbon_x + x_offset), int(self.ribbon_y + self.ribbon_height / 2))
    
    def schedule_announcement_update(self):
        """Schedule announcement updates"""
        self.update_announcement()
    
    def update_announcement(self):
        """Update the scrolling announcement text - scroll all at once"""
        _t0 = datetime.now() if ENABLE_PERF_TRACE else None
        try:
            # Handle hidden phase: wait for hide duration then unhide
            if self.news_tape_hidden:
                import time as _time
                elapsed = _time.time() - self.news_tape_hide_start
                if elapsed >= self.news_tape_hide_duration:
                    self.news_tape_hidden = False
                    self.announcement_x_pos = 0
                    self.redraw_full_display()
                # Skip scrolling while hidden
            elif self.announcement_text_ids and len(self.announcement_text_ids) > 0:
                try:
                    # Move all text objects left
                    self.announcement_x_pos -= 7  # Scroll speed (faster)
                    
                    # Update position for all text objects
                    for i, (text_id, text, color, width) in enumerate(self.announcement_text_ids):
                        if i < len(self.announcement_x_positions):
                            x_offset = self.announcement_x_pos + self.announcement_x_positions[i]
                            self.canvas.coords(
                                text_id,
                                int(self.ribbon_x + x_offset),
                                int(self.ribbon_y + self.ribbon_height/2)
                            )
                    
                    # Check if all text has scrolled off screen
                    if self.announcement_x_pos < -self.announcement_total_width:
                        if self.news_tape_hide_duration > 0:
                            # Enter hide phase
                            import time as _time
                            self.news_tape_hidden = True
                            self.news_tape_hide_start = _time.time()
                            self.announcement_text_ids = []
                            self.redraw_full_display()
                        else:
                            # No hide - loop immediately
                            self.announcement_x_pos = self.ribbon_width
                        
                except Exception as e:
                    self.announcement_text_ids = []
        except Exception as e:
            self.announcement_text_ids = []
        
        # Schedule next update in stable cadence
        try:
            self.root.after(self.announcement_tick_ms, self.update_announcement)
        except:
            pass

        if ENABLE_PERF_TRACE and _t0 is not None:
            elapsed_ms = (datetime.now() - _t0).total_seconds() * 1000
            if elapsed_ms > 50:
                last_ts = self._perf_last_log.get('update_announcement', 0)
                now_ts = datetime.now().timestamp()
                if now_ts - last_ts >= 2:
                    self._perf_last_log['update_announcement'] = now_ts
                    self._log(f"[PERF] update_announcement slow: {elapsed_ms:.1f}ms")
    
    def update_yellow_ribbon(self):
        """Update the scrolling yellow ribbon text - scroll continuously"""
        _t0 = datetime.now() if ENABLE_PERF_TRACE else None
        try:
            eid_event = self.get_active_eid_salah_event()
            # Handle hidden phase: wait for hide duration then unhide
            if self.yellow_ribbon_hidden:
                import time as _time
                elapsed = _time.time() - self.yellow_ribbon_hide_start
                if elapsed >= self.news_tape_hide_duration:
                    self.yellow_ribbon_hidden = False
                    self.yellow_ribbon_x_pos = 0
                    self.redraw_full_display()
                # Skip scrolling while hidden
            elif self.yellow_ribbon_text_ids and len(self.yellow_ribbon_text_ids) > 0:
                try:
                    # Eid alternates language passes with opposite directions.
                    step = 7
                    if eid_event:
                        self.yellow_ribbon_x_pos += (step * self.eid_ribbon_direction)
                    else:
                        self.yellow_ribbon_x_pos -= step  # Match announcement scroll speed
                    
                    # Update position for all text objects
                    for i, (text_id, text, color, width) in enumerate(self.yellow_ribbon_text_ids):
                        if i < len(self.yellow_ribbon_x_positions):
                            x_offset = self.yellow_ribbon_x_pos + self.yellow_ribbon_x_positions[i]
                            self.canvas.coords(
                                text_id,
                                int(self.yellow_ribbon_x + x_offset),
                                int(self.yellow_ribbon_y + self.yellow_ribbon_height/2)
                            )
                    
                    # Check if all text has scrolled off screen
                    if eid_event:
                        completed = False
                        if self.eid_ribbon_direction < 0 and self.yellow_ribbon_x_pos < -self.yellow_ribbon_total_width:
                            completed = True
                        # For left-to-right pass, x_pos > 0 means the whole message has exited.
                        if self.eid_ribbon_direction > 0 and self.yellow_ribbon_x_pos > 0:
                            completed = True

                        if completed:
                            if self.eid_ribbon_phase == 'english':
                                # Immediately follow with Arabic pass.
                                self.eid_ribbon_phase = 'arabic'
                                self.yellow_ribbon_x_pos = 0
                                self.redraw_full_display()
                            else:
                                # Arabic finished; return to English and apply configured hide cycle.
                                self.eid_ribbon_phase = 'english'
                                if self.news_tape_hide_duration > 0:
                                    import time as _time
                                    self.yellow_ribbon_hidden = True
                                    self.yellow_ribbon_hide_start = _time.time()
                                    self.yellow_ribbon_text_ids = []
                                    self.redraw_full_display()
                                else:
                                    self.yellow_ribbon_x_pos = 0
                                    self.redraw_full_display()
                    elif self.yellow_ribbon_x_pos < -self.yellow_ribbon_total_width:
                        if self.news_tape_hide_duration > 0:
                            # Enter hide phase
                            import time as _time
                            self.yellow_ribbon_hidden = True
                            self.yellow_ribbon_hide_start = _time.time()
                            self.yellow_ribbon_text_ids = []
                            self.redraw_full_display()
                        else:
                            # No hide - loop immediately
                            self.yellow_ribbon_x_pos = self.yellow_ribbon_width
                        
                except Exception as e:
                    self.yellow_ribbon_text_ids = []
        except Exception as e:
            self.yellow_ribbon_text_ids = []
        
        # Schedule next update in stable cadence
        try:
            self.root.after(self.yellow_ribbon_tick_ms, self.update_yellow_ribbon)
        except:
            pass

        if ENABLE_PERF_TRACE and _t0 is not None:
            elapsed_ms = (datetime.now() - _t0).total_seconds() * 1000
            if elapsed_ms > 50:
                last_ts = self._perf_last_log.get('update_yellow_ribbon', 0)
                now_ts = datetime.now().timestamp()
                if now_ts - last_ts >= 2:
                    self._perf_last_log['update_yellow_ribbon'] = now_ts
                    self._log(f"[PERF] update_yellow_ribbon slow: {elapsed_ms:.1f}ms")
    
    def schedule_yellow_ribbon_update(self):
        """Schedule yellow ribbon scrolling updates"""
        self.update_yellow_ribbon()
    
    def draw_star_pattern(self, width, height):
        """Draw repeating 8-pointed star pattern"""
        # Pattern spacing
        spacing_x = 120
        spacing_y = 120
        star_size = 40
        
        # Calculate grid
        start_x = -spacing_x
        start_y = -spacing_y
        
        # Draw stars in a grid
        y = start_y
        while y < height + spacing_y:
            x = start_x
            row_offset = (y // spacing_y) % 2
            x_offset = spacing_x / 2 if row_offset else 0
            
            while x < width + spacing_x:
                self.draw_8_point_star(x + x_offset, y, star_size, '#1e3a5f', 0.15)
                x += spacing_x
            y += spacing_y
    
    def draw_8_point_star(self, cx, cy, size, color, opacity):
        """Draw an 8-pointed Islamic star"""
        points = []
        outer_radius = size
        inner_radius = size * 0.4
        
        # Create 8-pointed star
        for i in range(16):
            angle = (i * math.pi / 8) - math.pi / 2
            if i % 2 == 0:
                radius = outer_radius
            else:
                radius = inner_radius
            
            x = cx + radius * math.cos(angle)
            y = cy + radius * math.sin(angle)
            points.extend([x, y])
        
        # Draw star with opacity simulation (lighter color)
        self.canvas.create_polygon(
            points, 
            fill=color, 
            outline='#2a4a6f',
            width=1,
            stipple='gray25'  # Creates semi-transparent effect
        )
    
    def draw_border_decoration(self, width, height):
        """Draw decorative star borders"""
        star_color = '#2a5a8f'
        star_size = 15
        spacing = 80
        
        # Top border with stars
        for i in range(int(spacing/2), int(width), spacing):
            self.draw_border_star(i, 20, star_size, star_color)
        
        # Bottom border with stars
        for i in range(int(spacing/2), int(width), spacing):
            self.draw_border_star(i, height - 20, star_size, star_color)
        
        # Left border with stars
        for i in range(int(spacing/2), int(height), spacing):
            self.draw_border_star(20, i, star_size, star_color)
        
        # Right border with stars
        for i in range(int(spacing/2), int(height), spacing):
            self.draw_border_star(width - 20, i, star_size, star_color)
    
    def draw_border_star(self, cx, cy, size, color):
        """Draw a decorative star for borders"""
        points = []
        for i in range(8):
            angle = (i * math.pi / 4) - math.pi / 2
            if i % 2 == 0:
                radius = size
            else:
                radius = size * 0.4
            
            x = cx + radius * math.cos(angle)
            y = cy + radius * math.sin(angle)
            points.extend([x, y])
        
        self.canvas.create_polygon(
            points,
            fill=color,
            outline='#3a6a9f',
            width=1,
            stipple='gray50'
        )
    
    def draw_corner_ornaments(self, width, height):
        """Draw ornamental corners"""
        ornament_size = 80
        color = '#2a5a8f'
        
        # Top-left corner
        self.draw_corner_ornament(ornament_size, ornament_size, ornament_size, color, 'tl')
        
        # Top-right corner
        self.draw_corner_ornament(width - ornament_size, ornament_size, ornament_size, color, 'tr')
        
        # Bottom-left corner
        self.draw_corner_ornament(ornament_size, height - ornament_size, ornament_size, color, 'bl')
        
        # Bottom-right corner
        self.draw_corner_ornament(width - ornament_size, height - ornament_size, ornament_size, color, 'br')
    
    def draw_corner_ornament(self, cx, cy, size, color, position):
        """Draw a single corner ornament"""
        # Draw concentric arcs
        for i in range(3):
            radius = size - (i * 15)
            self.canvas.create_oval(
                cx - radius/2, cy - radius/2,
                cx + radius/2, cy + radius/2,
                outline=color,
                width=2,
                stipple='gray50'
            )
        
        # Draw radiating lines
        angles = [0, 45, 90, 135, 180, 225, 270, 315]
        for angle in angles:
            rad = math.radians(angle)
            x1 = cx + (size * 0.2) * math.cos(rad)
            y1 = cy + (size * 0.2) * math.sin(rad)
            x2 = cx + (size * 0.5) * math.cos(rad)
            y2 = cy + (size * 0.5) * math.sin(rad)
            
            self.canvas.create_line(
                x1, y1, x2, y2,
                fill=color,
                width=1,
                stipple='gray50'
            )
        
        # Center circle
        center_size = 10
        self.canvas.create_oval(
            cx - center_size, cy - center_size,
            cx + center_size, cy + center_size,
            fill=color,
            outline='#3a6a9f',
            width=2
        )
    
    def draw_crescents(self, width, height):
        """Draw crescent moons at various positions"""
        crescents = [
            # Top row - enhanced with more crescents and size variety
            (width * 0.05, height * 0.08, 28, '#2a5a8f'),
            (width * 0.12, height * 0.05, 20, '#1e4a7f'),
            (width * 0.20, height * 0.09, 35, '#2a6a9f'),
            (width * 0.28, height * 0.06, 24, '#1e4a7f'),
            (width * 0.37, height * 0.08, 30, '#2a5a8f'),
            (width * 0.46, height * 0.05, 42, '#2a6a9f'),
            (width * 0.54, height * 0.07, 26, '#1e4a7f'),
            (width * 0.63, height * 0.09, 32, '#2a5a8f'),
            (width * 0.72, height * 0.06, 28, '#2a6a9f'),
            (width * 0.80, height * 0.08, 25, '#1e4a7f'),
            (width * 0.88, height * 0.05, 38, '#2a5a8f'),
            (width * 0.95, height * 0.09, 22, '#2a6a9f'),
            
            # Upper middle row - enhanced
            (width * 0.04, height * 0.18, 26, '#1e4a7f'),
            (width * 0.11, height * 0.22, 18, '#2a5a8f'),
            (width * 0.19, height * 0.20, 30, '#2a6a9f'),
            (width * 0.27, height * 0.24, 22, '#1e4a7f'),
            (width * 0.36, height * 0.19, 28, '#2a5a8f'),
            (width * 0.45, height * 0.23, 20, '#2a6a9f'),
            (width * 0.55, height * 0.21, 24, '#1e4a7f'),
            (width * 0.64, height * 0.24, 32, '#2a5a8f'),
            (width * 0.73, height * 0.20, 26, '#2a6a9f'),
            (width * 0.81, height * 0.22, 29, '#1e4a7f'),
            (width * 0.90, height * 0.19, 23, '#2a5a8f'),
            (width * 0.96, height * 0.23, 27, '#2a6a9f'),
            
            # Middle row - enhanced with more variety
            (width * 0.06, height * 0.45, 30, '#2a5a8f'),
            (width * 0.14, height * 0.48, 24, '#1e4a7f'),
            (width * 0.22, height * 0.46, 19, '#2a6a9f'),
            (width * 0.31, height * 0.50, 28, '#1e4a7f'),
            (width * 0.40, height * 0.47, 22, '#2a5a8f'),
            (width * 0.50, height * 0.51, 26, '#2a6a9f'),
            (width * 0.60, height * 0.48, 25, '#1e4a7f'),
            (width * 0.69, height * 0.50, 31, '#2a5a8f'),
            (width * 0.78, height * 0.46, 23, '#2a6a9f'),
            (width * 0.86, height * 0.49, 29, '#1e4a7f'),
            (width * 0.94, height * 0.47, 27, '#2a5a8f'),
            
            # Lower middle row - enhanced
            (width * 0.05, height * 0.65, 25, '#2a6a9f'),
            (width * 0.13, height * 0.68, 21, '#1e4a7f'),
            (width * 0.21, height * 0.70, 33, '#2a5a8f'),
            (width * 0.30, height * 0.67, 27, '#2a6a9f'),
            (width * 0.39, height * 0.72, 23, '#1e4a7f'),
            (width * 0.50, height * 0.69, 35, '#2a5a8f'),
            (width * 0.61, height * 0.71, 26, '#2a6a9f'),
            (width * 0.70, height * 0.68, 29, '#1e4a7f'),
            (width * 0.79, height * 0.72, 24, '#2a5a8f'),
            (width * 0.87, height * 0.69, 31, '#2a6a9f'),
            (width * 0.95, height * 0.67, 28, '#1e4a7f'),
            
            # Bottom row - enhanced with more crescents
            (width * 0.04, height * 0.85, 32, '#2a5a8f'),
            (width * 0.12, height * 0.89, 26, '#1e4a7f'),
            (width * 0.20, height * 0.87, 22, '#2a6a9f'),
            (width * 0.29, height * 0.91, 28, '#1e4a7f'),
            (width * 0.38, height * 0.88, 25, '#2a5a8f'),
            (width * 0.47, height * 0.92, 40, '#2a6a9f'),
            (width * 0.53, height * 0.90, 24, '#1e4a7f'),
            (width * 0.62, height * 0.93, 30, '#2a5a8f'),
            (width * 0.71, height * 0.89, 27, '#2a6a9f'),
            (width * 0.79, height * 0.91, 23, '#1e4a7f'),
            (width * 0.88, height * 0.88, 36, '#2a5a8f'),
            (width * 0.96, height * 0.90, 29, '#2a6a9f'),
        ]
        
        for x, y, size, color in crescents:
            self.draw_crescent_moon(x, y, size, color)
    
    def draw_crescent_moon(self, x, y, size, color):
        """Draw Islamic crescent moon symbol"""
        # Outer circle
        self.canvas.create_oval(
            x - size, y - size,
            x + size, y + size,
            fill=color, outline='', stipple='gray50'
        )
        
        # Inner circle to create crescent
        offset = size * 0.4
        self.canvas.create_oval(
            x - size + offset, y - size + offset * 0.2,
            x + size + offset, y + size + offset * 0.2,
            fill='#6888b8', outline=''
        )
        
        # Add star next to crescent
        star_x = x + size * 1.3
        star_y = y - size * 0.5
        self.draw_small_star(star_x, star_y, size * 0.3, color)
    
    def draw_five_pointed_stars(self, width, height):
        """Draw 5-pointed stars of various sizes across the background"""
        stars = [
            # Top area - more scattered stars with size variety
            (width * 0.03, height * 0.12, 14, '#2a5a8f'),
            (width * 0.08, height * 0.08, 8, '#1e4a7f'),
            (width * 0.14, height * 0.13, 18, '#2a6a9f'),
            (width * 0.24, height * 0.10, 11, '#1e4a7f'),
            (width * 0.31, height * 0.14, 16, '#2a5a8f'),
            (width * 0.40, height * 0.11, 9, '#2a6a9f'),
            (width * 0.48, height * 0.13, 20, '#1e4a7f'),
            (width * 0.56, height * 0.09, 13, '#2a5a8f'),
            (width * 0.66, height * 0.14, 10, '#2a6a9f'),
            (width * 0.74, height * 0.11, 17, '#1e4a7f'),
            (width * 0.83, height * 0.13, 12, '#2a5a8f'),
            (width * 0.91, height * 0.10, 15, '#2a6a9f'),
            (width * 0.97, height * 0.12, 11, '#1e4a7f'),
            
            # Upper middle area - enhanced
            (width * 0.07, height * 0.27, 13, '#1e4a7f'),
            (width * 0.15, height * 0.30, 9, '#2a5a8f'),
            (width * 0.23, height * 0.28, 16, '#2a6a9f'),
            (width * 0.33, height * 0.32, 11, '#1e4a7f'),
            (width * 0.42, height * 0.29, 14, '#2a5a8f'),
            (width * 0.52, height * 0.31, 10, '#2a6a9f'),
            (width * 0.58, height * 0.28, 18, '#1e4a7f'),
            (width * 0.67, height * 0.32, 12, '#2a5a8f'),
            (width * 0.77, height * 0.29, 15, '#2a6a9f'),
            (width * 0.85, height * 0.31, 8, '#1e4a7f'),
            (width * 0.93, height * 0.28, 13, '#2a5a8f'),
            
            # Middle area - enhanced with more stars
            (width * 0.10, height * 0.53, 17, '#2a5a8f'),
            (width * 0.17, height * 0.49, 12, '#1e4a7f'),
            (width * 0.26, height * 0.54, 10, '#2a6a9f'),
            (width * 0.34, height * 0.51, 15, '#1e4a7f'),
            (width * 0.43, height * 0.56, 11, '#2a5a8f'),
            (width * 0.50, height * 0.52, 19, '#2a6a9f'),
            (width * 0.57, height * 0.55, 13, '#1e4a7f'),
            (width * 0.66, height * 0.51, 9, '#2a5a8f'),
            (width * 0.74, height * 0.54, 16, '#2a6a9f'),
            (width * 0.83, height * 0.52, 14, '#1e4a7f'),
            (width * 0.90, height * 0.55, 11, '#2a5a8f'),
            
            # Lower middle area - enhanced
            (width * 0.09, height * 0.73, 15, '#2a6a9f'),
            (width * 0.16, height * 0.76, 10, '#1e4a7f'),
            (width * 0.24, height * 0.74, 18, '#2a5a8f'),
            (width * 0.33, height * 0.77, 13, '#2a6a9f'),
            (width * 0.43, height * 0.75, 11, '#1e4a7f'),
            (width * 0.52, height * 0.78, 20, '#2a5a8f'),
            (width * 0.58, height * 0.74, 14, '#2a6a9f'),
            (width * 0.67, height * 0.77, 9, '#1e4a7f'),
            (width * 0.76, height * 0.75, 17, '#2a5a8f'),
            (width * 0.84, height * 0.78, 12, '#2a6a9f'),
            (width * 0.92, height * 0.74, 15, '#1e4a7f'),
            
            # Bottom area - enhanced
            (width * 0.06, height * 0.91, 16, '#2a5a8f'),
            (width * 0.14, height * 0.94, 11, '#1e4a7f'),
            (width * 0.24, height * 0.92, 14, '#2a6a9f'),
            (width * 0.32, height * 0.95, 9, '#1e4a7f'),
            (width * 0.42, height * 0.93, 19, '#2a5a8f'),
            (width * 0.51, height * 0.96, 13, '#2a6a9f'),
            (width * 0.59, height * 0.94, 10, '#1e4a7f'),
            (width * 0.68, height * 0.92, 17, '#2a5a8f'),
            (width * 0.76, height * 0.95, 12, '#2a6a9f'),
            (width * 0.85, height * 0.93, 15, '#1e4a7f'),
            (width * 0.94, height * 0.91, 18, '#2a5a8f'),
        ]
        
        for x, y, size, color in stars:
            self.draw_small_star(x, y, size, color)
    
    def draw_small_star(self, cx, cy, size, color, tags=None):
        """Draw a small 5-pointed star"""
        points = []
        for i in range(10):
            angle = (i * math.pi / 5) - math.pi / 2
            radius = size if i % 2 == 0 else size * 0.4
            x = cx + radius * math.cos(angle)
            y = cy + radius * math.sin(angle)
            points.extend([x, y])
        
        self.canvas.create_polygon(
            points, fill=color, outline='', stipple='gray50', tags=tags
        )

    def draw_hd_star(self, cx, cy, size, color, tags=None):
        """Draw a higher-quality pointed star with glow (no cross rays)."""
        points = []
        for i in range(10):
            angle = (i * math.pi / 5) - (math.pi / 2)
            radius = size if i % 2 == 0 else size * 0.43
            points.extend([
                cx + (radius * math.cos(angle)),
                cy + (radius * math.sin(angle))
            ])

        self.canvas.create_polygon(
            points,
            fill=color,
            outline=self._mix_hex_color(color, '#ffffff', 0.35),
            width=1,
            tags=tags
        )
    
    def draw_mosques(self, width, height):
        """Draw minarets at various positions"""
        # Multiple minarets around the display
        minarets = [
            # Left side
            (width * 0.05, height * 0.40, 10, 100, '#1a3a5f'),
            (width * 0.08, height * 0.55, 12, 120, '#2a4a7f'),
            (width * 0.05, height * 0.70, 10, 95, '#1a3a5f'),
            
            # Right side
            (width * 0.95, height * 0.40, 10, 100, '#2a4a7f'),
            (width * 0.92, height * 0.55, 12, 120, '#1a3a5f'),
            (width * 0.95, height * 0.70, 10, 95, '#2a4a7f'),
            
            # Top corners
            (width * 0.12, height * 0.20, 9, 85, '#1a3a5f'),
            (width * 0.88, height * 0.20, 9, 85, '#2a4a7f'),
            
            # Bottom corners
            (width * 0.15, height * 0.85, 11, 110, '#2a4a7f'),
            (width * 0.85, height * 0.85, 11, 110, '#1a3a5f'),
        ]
        
        for x, y, width_val, height_val, color in minarets:
            self.draw_minaret(x, y, width_val, height_val, color)
    
    def draw_mosque(self, x, y, size, color):
        """Deprecated - kept for compatibility"""
        pass
    
    def draw_minaret(self, x, y, width, height, color):
        """Draw a minaret tower"""
        # Tower body
        self.canvas.create_rectangle(
            x - width/2, y - height,
            x + width/2, y,
            fill=color, outline=''
        )
        
        # Top dome
        dome_radius = width * 0.8
        self.canvas.create_oval(
            x - dome_radius, y - height - dome_radius,
            x + dome_radius, y - height + dome_radius,
            fill=color, outline=''
        )
        
        # Crescent on top
        crescent_size = width * 0.5
        self.canvas.create_oval(
            x - crescent_size, y - height - dome_radius * 2,
            x + crescent_size, y - height - dome_radius * 2 + crescent_size * 2,
            fill=color, outline=''
        )
    
    def draw_calligraphy(self, width, height):
        """Draw decorative Arabic text in background"""
        # Arabic phrases for decorative background
        arabic_texts = [
            'الصلاة نور',  # Prayer is light
            'السلام عليكم',  # Peace be upon you
            'ماشاء الله',  # What Allah wills
            'بارك الله',  # Allah's blessing
            'الحمد لله',  # Praise be to Allah
            'رحمة الله',  # Allah's mercy
            'في أمان الله',  # In Allah's protection
        ]
        
        # Create flowing Arabic text pattern across the background
        text_positions = [
            # Top section
            (width * 0.25, height * 0.20, 48, 0, 'gray25'),
            (width * 0.75, height * 0.20, 42, 0, 'gray25'),
            
            # Middle section - larger and more prominent
            (width * 0.15, height * 0.45, 56, -15, 'gray12'),
            (width * 0.50, height * 0.50, 64, 0, 'gray12'),
            (width * 0.85, height * 0.45, 52, 15, 'gray12'),
            
            # Lower section
            (width * 0.30, height * 0.75, 46, 0, 'gray25'),
            (width * 0.70, height * 0.75, 50, 0, 'gray25'),
            
            # Diagonal flowing text
            (width * 0.10, height * 0.30, 38, -30, 'gray50'),
            (width * 0.90, height * 0.70, 40, 30, 'gray50'),
        ]
        
        for idx, (x, y, size, angle, stipple) in enumerate(text_positions):
            text = arabic_texts[idx % len(arabic_texts)]
            
            # Create text with rotation and transparency effect
            text_id = self.canvas.create_text(
                x, y,
                text=text,
                font=('Arial', size, 'bold'),
                fill='#1e4a7f',
                stipple=stipple,
                angle=angle
            )


def main():
    try:
        acquire_single_instance_lock()

        root = tk.Tk()
        app = IslamicBackground(root)
        root.mainloop()
    except Exception as e:
        try:
            import traceback
            error_text = traceback.format_exc()
            with open('error_log.txt', 'a', encoding='utf-8') as f:
                f.write(f"\n[{datetime.now().isoformat()}] Unhandled exception in main()\n")
                f.write(error_text)
                f.write("\n")
            try:
                messagebox.showerror('Prayer Times Display Error', f"{e}\n\nDetails saved to error_log.txt")
            except:
                pass
            print(error_text, file=sys.stderr)
        except:
            pass


if __name__ == '__main__':
    main()
