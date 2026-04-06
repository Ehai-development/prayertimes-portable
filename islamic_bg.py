"""
Prayer Times Display - Building from Scratch
Step 1: Islamic Background Design
"""

import tkinter as tk
from tkinter import Canvas
from tkinter import font as tkfont
import math
import csv
import json
import re
import sys
import socket
import time
from datetime import datetime, timedelta
from pathlib import Path
from PIL import Image, ImageTk, ImageDraw
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
        self.root.attributes('-fullscreen', True)
        self.root.configure(bg='#2c1169')
        
        # Keyboard bindings
        self.root.bind('<Escape>', lambda e: self.root.attributes('-fullscreen', False))
        self.root.bind('<F11>', lambda e: self.root.attributes('-fullscreen', True))
        self.root.bind('q', lambda e: self.root.quit())
        self.root.bind('Q', lambda e: self.root.quit())
        
        # Create the canvas for drawing
        self.canvas = Canvas(root, bg='#2c1169', highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # Force window update so canvas has correct dimensions
        self.root.update_idletasks()
        
        # Bind resize event
        self.canvas.bind('<Configure>', self.on_resize)

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
        self.next_prayer_line_font = tkfont.Font(family='Arial', size=20, weight='bold')
        self.next_prayer_prefix_font = tkfont.Font(family='Arial', size=18, weight='bold')
        self.next_prayer_countdown_fixed_width = self.next_prayer_line_font.measure('88:88:88')
        self.next_prayer_static_width = None
        self._next_prayer_last_text_parts = None
        self._next_prayer_last_widths = (0, 0, 0, 0)
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
        self.iqamah_overlay_mode = None  # 'countdown' or 'post'
        self.iqamah_post_duration_seconds = 180
        self.iqamah_overlay_cooldown_until = None
        self.iqamah_overlay_last_update = 0  # Timestamp to prevent rapid updates
        
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
        
        # Tracking for prayer time changes (tomorrow vs today)
        self.changing_prayers = {}  # {prayer_name: {today: time, tomorrow: time}}
        self.announcement_scroll_complete = False
        
        # Red ribbon visibility cycle (15 sec ON, 15 sec OFF)
        self.ribbon_cycle_counter = 0  # 0-29 seconds
        self.ribbon_visible = True  # Start visible
        
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
        
        # Jummah time (loaded from CSV or config/jummah.txt)
        self.jummah_time = None

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
            if self.show_weather:
                self.root.after(500, self._start_weather_fetch)
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
            self.root.attributes('-fullscreen', True)
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
            # Redraw in proper z-order: background first, then foreground content
            self.canvas.delete('all')
            self.draw_islamic_background()
            self.draw_prayer_times()
            self.draw_test_mode_indicator()

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
            self.draw_islamic_background()
            self.draw_prayer_times()
            self.draw_test_mode_indicator()
            # Re-show iqamah overlay if it was active (canvas.delete wiped it)
            if overlay_was_visible:
                self.iqamah_overlay_ids = []
                if overlay_mode == 'post':
                    self.show_post_iqamah_overlay()
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
                "theme": "moon",
                "arabicchangeevery": 30,
                "arabicnameduration": 5
            }

        # Visual theme selection
        theme_name = str(self.config.get('theme', 'moon')).strip().lower()
        if theme_name in ('elegent', 'elegant'):
            theme_name = 'modern'
        if theme_name not in ('moon', 'modern', 'ramadan', 'elegent'):
            theme_name = 'moon'
        self.config['theme'] = theme_name

        # Optional full-screen background image path
        self.config['background_image'] = str(self.config.get('background_image', '')).strip()

        # Post-prayer overlay duration in minutes (configurable)
        try:
            prayernow_minutes = int(self.config.get('prayernow', 3))
            prayernow_minutes = max(0, prayernow_minutes)
        except:
            prayernow_minutes = 3
        self.config['prayernow'] = prayernow_minutes
        self.iqamah_post_duration_seconds = prayernow_minutes * 60

        # Athan callout flashing duration in seconds (0 disables callout flashing)
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
            arabic_name_duration_seconds = int(self.config.get('arabicnameduration', 5))
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
        """Save the background image log to config/background_log.json."""
        log_path = self.get_config_dir() / 'background_log.json'
        try:
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

                # If today already has an entry, return that image
                for img_name, date_shown in shown.items():
                    if date_shown == today_str:
                        match = next((f for f in bg_images if f.name == img_name), None)
                        if match:
                            return match.resolve()

                # Find images not yet shown in this cycle
                all_names = {f.name for f in bg_images}
                shown_names = set(shown.keys())
                remaining = all_names - shown_names

                # All shown — reset log and start fresh
                if not remaining:
                    shown = {}
                    remaining = all_names

                # Pick a random image from remaining
                chosen_name = random.choice(sorted(remaining))
                chosen_path = next(f for f in bg_images if f.name == chosen_name)

                # Log it
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
        top_y = height - self.us(170, 85)

        # Masjid name - large italic serif
        name_font = ('Georgia', self.fs(48, 24), 'bold italic')
        self.draw_outlined_text(
            cx, top_y, name_part,
            font=name_font, fill='white', outline='black', outline_px=2,
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
                font=loc_font, fill='white', outline='black', outline_px=1,
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
        if theme_name in ('elegent', 'elegant'):
            return 'modern'
        if theme_name not in ('moon', 'modern', 'ramadan', 'elegent'):
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
        base_csv_path = Path(__file__).parent / 'data' / self.config.get('data_file', 'prayer_times.csv')
        ramadan_csv_path = Path(__file__).parent / 'data' / 'Ramadan-prayer-timings-2026.csv'

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

        if is_friday:
            _, sunrise_time = self.resolve_sunrise_time(prayers_data)
            asr_athan = self.parse_time(prayers_data.get('AsrAthan', ''))
            friday_duhr_start = self.parse_time('2:15 PM')
            jummah_time = self.jummah_time or self.parse_time('1:30 PM')

            if sunrise_time and jummah_time and sunrise_time <= now < jummah_time:
                return 'Shrouq'

            if jummah_time and friday_duhr_start and jummah_time <= now < friday_duhr_start:
                return 'Jummah'

            if friday_duhr_start and asr_athan and friday_duhr_start <= now < asr_athan:
                return 'Duhr'

        # Current period boundaries by Athan-style starts, including Shrouq via Sunrise.
        # This keeps prayer highlighting consistent throughout each period.
        sunrise_value, sunrise_time = self.resolve_sunrise_time(prayers_data)
        prayer_schedule = [
            ('Fajr', self.parse_time(prayers_data.get('FajrAthan', ''))),
            ('Shrouq', sunrise_time),
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

        if is_friday:
            _, sunrise_time = self.resolve_sunrise_time(prayers_data)
            jummah_time = self.jummah_time or self.parse_time('1:30 PM')
            asr_athan = self.parse_time(prayers_data.get('AsrAthan', ''))

            if sunrise_time and jummah_time and sunrise_time <= current_time < jummah_time:
                return 'Jummah', jummah_time

            if jummah_time and asr_athan and jummah_time <= current_time < asr_athan:
                return 'Asr', asr_athan

        midday_name = 'Jummah' if is_friday else 'Duhr'

        # Include Shrouq (Sunrise) in the prayer progression
        _, sunrise_time = self.resolve_sunrise_time(prayers_data)
        prayer_schedule = [
            ('Fajr', self.parse_time(prayers_data.get('FajrAthan', ''))),
            ('Shrouq', sunrise_time),
            (midday_name, self.parse_time(prayers_data.get('DuhrAthan', ''))),
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

    def get_next_line_display_data(self, prayers_data):
        """Return dynamic label/name/countdown for next-prayer line.

        During the window between a prayer's Athan and Iqama, show:
        <PRAYER> IQAMAH IN <countdown to iqama>
        Otherwise show:
        NEXT PRAYER: <PRAYER> IN <countdown to athan>
        """
        try:
            now = self.get_current_time()
            is_friday = (self.get_current_date().weekday() == 4)
            current_prayer = self.get_current_prayer(prayers_data)

            show_arabic = bool(getattr(self, 'salah_names_show_arabic', False))
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

            next_prayer_name, next_athan = self.get_next_prayer(prayers_data)
            self.next_prayer_athan_time = next_athan
            if is_friday and next_prayer_name == 'Jummah':
                return {
                    'prefix_text': '',
                    'name_text': localized_phrase('Jummah khutbah', 'خطبة الجمعة'),
                    'in_text': localized_phrase(' in ', ' خلال '),
                    'countdown_text': self.get_countdown(next_athan),
                    'rtl': rtl_mode
                }
            return {
                'prefix_text': localized_phrase('Next prayer: ', 'الصلاة القادمة \u200f:\u200f '),
                'name_text': localized_prayer_name(next_prayer_name),
                'in_text': localized_phrase(' in ', ' خلال '),
                'countdown_text': self.get_countdown(next_athan),
                'rtl': rtl_mode
            }
        except:
            show_arabic = bool(getattr(self, 'salah_names_show_arabic', False))
            return {
                'prefix_text': 'الصلاة القادمة \u200f:\u200f ' if show_arabic else 'Next prayer: ',
                'name_text': '---',
                'in_text': ' خلال ' if show_arabic else ' in ',
                'countdown_text': '--:--:--',
                'rtl': show_arabic
            }

    def get_athan_blink_state(self, prayers_data):
        """Return active athan prayer during athan window, else (None, False)."""
        try:
            duration_seconds = int(self.config.get('athancalloutduran', 25))
            if duration_seconds <= 0 or not prayers_data:
                return None, False

            current_date = self.get_current_date()
            now_dt = datetime.combine(current_date, self.get_current_time())

            for prayer_name in ['Fajr', 'Duhr', 'Asr', 'Maghrib', 'Isha']:
                athan_time = self.parse_time(prayers_data.get(f'{prayer_name}Athan', ''))
                if not athan_time:
                    continue

                athan_dt = datetime.combine(current_date, athan_time)
                elapsed = (now_dt - athan_dt).total_seconds()

                # Active athan window for configured duration from athan time.
                if 0 <= elapsed < duration_seconds:
                    blink_visible = (int(elapsed) % 2 == 0)
                    return prayer_name, blink_visible
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
        self.athan_callout_box_id = None
        self.athan_callout_text_id = None
        self.athan_callout_prayer = None

    def update_athan_callout(self, athan_prayer=None, callout_visible=True):
        """Show ATHAN callout anchored to the active prayer box."""
        if (not athan_prayer
            or not callout_visible
            or athan_prayer not in self.prayer_box_bounds):
            self.clear_athan_callout()
            return

        try:
            x, y, width, _ = self.prayer_box_bounds[athan_prayer]
            callout_text = f"{athan_prayer.upper()} ATHAN TIME"
            text_font = ('Arial', self.fs(24, 12), 'bold')
            text_width = tkfont.Font(font=text_font).measure(callout_text)

            callout_height = self.us(40, 22)
            callout_width = max(self.us(180, 120), text_width + self.us(34, 20))
            callout_x = x + (width - callout_width) / 2
            callout_y = y - self.us(48, 28)

            self.clear_athan_callout()
            self.athan_callout_box_id = self.draw_rounded_rectangle(
                callout_x,
                callout_y,
                callout_width,
                callout_height,
                self.us(16, 8),
                fill='#d32f2f',
                outline='#b71c1c',
                outline_width=self.us(2, 1)
            )
            self.athan_callout_text_id = self.canvas.create_text(
                callout_x + (callout_width / 2),
                callout_y + (callout_height / 2),
                text=callout_text,
                font=text_font,
                fill='white'
            )
            self.athan_callout_prayer = athan_prayer
        except:
            self.clear_athan_callout()
    
    def schedule_countdown_update(self):
        """Schedule the countdown update to run every second"""
        self.update_countdown()
    
    def update_countdown(self):
        """Update the countdown text every second"""
        _t0 = datetime.now() if ENABLE_PERF_TRACE else None
        try:
            current_date = self.get_current_date()
            if current_date != self._last_seen_date:
                self.handle_date_rollover(current_date)

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

                    if self.iqamah_overlay_visible:
                        self.update_athan_callout(None)
                    else:
                        self.update_athan_callout(blinking_prayer, blink_visible)

                    if current_prayer_now != self.last_rendered_current_prayer:
                        self.last_rendered_current_prayer = current_prayer_now
                        self.update_prayer_box_highlight_states(current_prayer_now, blinking_prayer, blink_visible)
                    elif not self.iqamah_overlay_visible:
                        self.update_prayer_box_highlight_states(current_prayer_now, blinking_prayer, blink_visible)

                    display_data = self.get_next_line_display_data(prayers_data)
                    prefix_text = display_data['prefix_text']
                    name_text = display_data['name_text']
                    in_text = display_data['in_text']
                    countdown_text = display_data['countdown_text']
                    rtl_mode = bool(display_data.get('rtl', False))

                    self.canvas.itemconfig(self.next_prayer_prefix_text_id, text=prefix_text, fill='black')
                    self.canvas.itemconfig(self.next_prayer_name_text_id, text=name_text, fill='#d32f2f')
                    self.canvas.itemconfig(self.next_prayer_in_text_id, text=in_text, fill='black')
                    self.canvas.itemconfig(self.countdown_text_id, text=countdown_text, fill='#2E7D32')

                    if self.next_prayer_line_x is not None and self.next_prayer_line_y is not None:
                        text_parts = (prefix_text, name_text, in_text, rtl_mode)
                        
                        # For RTL Arabic, keep segments separate but enforce a visible gap.
                        if rtl_mode:
                            rtl_gap = self.us(18, 9)
                            if text_parts != self._next_prayer_last_text_parts:
                                prefix_width = self.next_prayer_prefix_font.measure(prefix_text)
                                name_width = self.next_prayer_line_font.measure(name_text)
                                in_width = self.next_prayer_line_font.measure(in_text)
                                countdown_width = self.next_prayer_countdown_fixed_width
                                self._next_prayer_last_text_parts = text_parts
                                self._next_prayer_last_widths = (prefix_width, name_width, in_width, countdown_width)
                                static_total_width = prefix_width + name_width + in_width + countdown_width + (rtl_gap * 3)
                                unconstrained_static_width = max(260, static_total_width + (self.next_prayer_panel_padding_x * 2))
                                if self.next_prayer_max_panel_width:
                                    self.next_prayer_static_width = min(unconstrained_static_width, self.next_prayer_max_panel_width)
                                else:
                                    self.next_prayer_static_width = unconstrained_static_width
                            else:
                                prefix_width, name_width, in_width, countdown_width = self._next_prayer_last_widths
                            total_width = prefix_width + name_width + in_width + countdown_width + (rtl_gap * 3)
                        else:
                            # For LTR English, keep separate measurements as before
                            if text_parts != self._next_prayer_last_text_parts:
                                prefix_width = self.next_prayer_prefix_font.measure(prefix_text)
                                name_width = self.next_prayer_line_font.measure(name_text)
                                in_width = self.next_prayer_line_font.measure(in_text)
                                countdown_width = self.next_prayer_countdown_fixed_width
                                self._next_prayer_last_text_parts = text_parts
                                self._next_prayer_last_widths = (prefix_width, name_width, in_width, countdown_width)
                                static_total_width = prefix_width + name_width + in_width + countdown_width
                                unconstrained_static_width = max(260, static_total_width + (self.next_prayer_panel_padding_x * 2))
                                if self.next_prayer_max_panel_width:
                                    self.next_prayer_static_width = min(unconstrained_static_width, self.next_prayer_max_panel_width)
                                else:
                                    self.next_prayer_static_width = unconstrained_static_width
                            else:
                                prefix_width, name_width, in_width, countdown_width = self._next_prayer_last_widths
                            total_width = prefix_width + name_width + in_width + countdown_width

                        left_x = self.next_prayer_line_x - (total_width / 2)
                        right_x = self.next_prayer_line_x + (total_width / 2)

                        # Keep panel width stable during per-second countdown ticks.
                        base_panel_width = self.next_prayer_static_width if self.next_prayer_static_width else max(260, total_width + (self.next_prayer_panel_padding_x * 2))
                        if self.next_prayer_max_panel_width:
                            panel_width = min(base_panel_width, self.next_prayer_max_panel_width)
                        else:
                            panel_width = base_panel_width
                        panel_x1 = self.next_prayer_line_x - (panel_width / 2)
                        panel_y1 = self.next_prayer_line_y - (self.next_prayer_panel_height / 2)
                        self.next_prayer_panel_bounds = (panel_x1, panel_y1, panel_width, self.next_prayer_panel_height)

                        if self.next_prayer_panel_width != panel_width:
                            if self.next_prayer_panel_id:
                                try:
                                    self.canvas.delete(self.next_prayer_panel_id)
                                except:
                                    pass

                            self.next_prayer_panel_id = self.draw_rounded_rectangle(
                                panel_x1, panel_y1, panel_width, self.next_prayer_panel_height, self.next_prayer_panel_radius,
                                fill='white', outline='#2a5a8f', outline_width=3
                            )
                            self.next_prayer_panel_width = panel_width
                            self.canvas.tag_lower(self.next_prayer_panel_id, self.next_prayer_prefix_text_id)

                        if rtl_mode:
                            rtl_gap = self.us(18, 9)
                            self.canvas.itemconfig(self.next_prayer_prefix_text_id, state='normal', anchor='e')
                            self.canvas.itemconfig(self.next_prayer_name_text_id, state='normal', anchor='e')
                            self.canvas.itemconfig(self.next_prayer_in_text_id, state='normal', anchor='e')
                            self.canvas.itemconfig(self.countdown_text_id, state='normal', anchor='e')
                            self.canvas.coords(self.next_prayer_prefix_text_id, right_x, self.next_prayer_line_y)
                            self.canvas.coords(self.next_prayer_name_text_id, right_x - prefix_width - rtl_gap, self.next_prayer_line_y)
                            self.canvas.coords(self.next_prayer_in_text_id, right_x - prefix_width - rtl_gap - name_width - rtl_gap, self.next_prayer_line_y)
                            self.canvas.coords(self.countdown_text_id, right_x - prefix_width - rtl_gap - name_width - rtl_gap - in_width - rtl_gap, self.next_prayer_line_y)
                        else:
                            # For English LTR: use separate positioned text elements
                            self.canvas.itemconfig(self.next_prayer_prefix_text_id, state='normal', anchor='w')
                            self.canvas.itemconfig(self.next_prayer_name_text_id, state='normal', anchor='w')
                            self.canvas.itemconfig(self.next_prayer_in_text_id, state='normal', anchor='w')
                            self.canvas.itemconfig(self.countdown_text_id, state='normal', anchor='w')
                            self.canvas.coords(self.next_prayer_prefix_text_id, left_x, self.next_prayer_line_y)
                            self.canvas.coords(self.next_prayer_name_text_id, left_x + prefix_width, self.next_prayer_line_y)
                            self.canvas.coords(self.next_prayer_in_text_id, left_x + prefix_width + name_width, self.next_prayer_line_y)
                            self.canvas.coords(self.countdown_text_id, left_x + prefix_width + name_width + in_width, self.next_prayer_line_y)
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

            # After post-iqamah phase ends, keep app on main page for a short cooldown
            if self.iqamah_overlay_cooldown_until and now_dt < self.iqamah_overlay_cooldown_until:
                if self.iqamah_overlay_visible:
                    self.hide_iqamah_overlay()
                self.root.after(1000, self.check_iqamah_countdown)
                return

            for prayer in overlay_prayers:
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

                if prayer == 'Duhr' and is_friday:
                    time_until_jummah = (iqamah_dt - now_dt).total_seconds()
                    if 0 < time_until_jummah <= 120:
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

            if pre_countdown_prayer:
                self.current_prayer_name = pre_countdown_prayer
                iqamah_dt = datetime.combine(mocked_date, self.current_prayer_iqamah_time)
                time_diff = (iqamah_dt - now_dt).total_seconds()

                # Show countdown overlay only in the last 2 minutes before iqamah
                if 0 < time_diff <= 120:
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
            is_friday_khutbah = (self.current_prayer_name == 'Jummah' and self.get_current_date().weekday() == 4)
            prayer_line_text = f"{self.current_prayer_name.upper()} iqamah in"
            instruction_line_text = 'Please put your cell phone on silent mode'
            instruction_font_size = self.fs(68, 32)
            iqamah_change_notice = self.get_iqamah_change_notice_text()

            if is_friday_khutbah:
                prayer_line_text = 'Jummah khutbah in'
                instruction_line_text = 'Talking is forbidden during Khutbahs'
                instruction_font_size = self.fs(74, 34)

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
                notice_font = ('Arial', self.fs(52, 24), 'bold')
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
            instruction_text = self.canvas.create_text(
                width / 2, notice_y,
                text=instruction_line_text,
                font=('Arial', instruction_font_size, 'bold'),
                fill='black',
                tags=('iqamah_overlay', 'iqamah_instruction_text')
            )
            self.iqamah_overlay_ids.append(instruction_text)

            # Larger centered no-phone icon beneath the notice
            icon_ids = self.draw_no_phone_icon(width / 2, icon_y, size=self.us(240, 130), tags='iqamah_overlay')
            
            # Raise overlay to top of canvas stacking order
            self.canvas.tag_raise('iqamah_overlay')
            
            self.iqamah_overlay_visible = True
            self.iqamah_overlay_mode = 'countdown'

            # Start English/Arabic text toggle for countdown overlay
            self._iqamah_countdown_lang_english = True
            self._iqamah_countdown_is_friday = is_friday_khutbah
            self._iqamah_countdown_prayer_name = self.current_prayer_name
            self._iqamah_countdown_toggle_id = self.root.after(10000, self._schedule_iqamah_countdown_text_toggle)

        except Exception as e:
            self._log(f"ERROR in show_iqamah_overlay: {e}")
            import traceback
            if getattr(self, 'show_logs', False): traceback.print_exc()

    def show_post_iqamah_overlay(self):
        """Show post-iqamah overlay for 3 minutes with ayah and prayer notice."""
        try:
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

            ayah_y = height * 0.24
            notice_y = ayah_y + self.us(185, 105)
            icon_y = notice_y + self.us(220, 125)
            prayer_now_y = time_bg_y + (_th + time_pad_y * 2) / 2

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

    def _schedule_iqamah_countdown_text_toggle(self):
        """Toggle instruction & prayer-line text on countdown overlay between English and Arabic every 5s."""
        if not self.iqamah_overlay_visible or self.iqamah_overlay_mode != 'countdown':
            self._iqamah_countdown_toggle_id = None
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
                instr = 'يُمنع الكلام أثناء الخطبة'
            else:
                prayer_line = f'إقامة {arabic_name} بعد'
                instr = 'يرجى وضع هاتفك على الوضع الصامت'
        for item_id in self.canvas.find_withtag('iqamah_prayer_line_text'):
            self.canvas.itemconfig(item_id, text=prayer_line)
        for item_id in self.canvas.find_withtag('iqamah_instruction_text'):
            self.canvas.itemconfig(item_id, text=instr)
        # English stays 10s, Arabic stays 5s
        delay = 10000 if self._iqamah_countdown_lang_english else 5000
        self._iqamah_countdown_toggle_id = self.root.after(delay, self._schedule_iqamah_countdown_text_toggle)

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
        for item_id in self.canvas.find_withtag('post_instruction_text'):
            self.canvas.itemconfig(item_id, text=instr)
        for item_id in self.canvas.find_withtag('post_prayer_now_text'):
            self.canvas.itemconfig(item_id, text=pnow)
        # English stays 10s, Arabic stays 5s
        delay = 10000 if self._post_overlay_lang_english else 5000
        self._post_overlay_toggle_id = self.root.after(delay, self._schedule_post_overlay_text_toggle)

    def clear_iqamah_overlay_items(self):
        """Delete overlay canvas items while preserving overlay state variables."""
        try:
            # Cancel text toggle timers
            for attr in ('_post_overlay_toggle_id', '_iqamah_countdown_toggle_id'):
                toggle_id = getattr(self, attr, None)
                if toggle_id:
                    self.root.after_cancel(toggle_id)
                    setattr(self, attr, None)
            for item_id in self.iqamah_overlay_ids:
                try:
                    self.canvas.delete(item_id)
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
            countdown = self.get_iqamah_countdown()

            # Hard transition: never remain on countdown overlay at 00:00
            if self.iqamah_overlay_mode == 'countdown' and countdown == '00:00':
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

        # Draw masjid name below the ayah and translation
        self.draw_outlined_text(
            width / 2, self.us(185),
            text=masjid_name,
            font=('Arial', self.fs(44, 18), 'bold'),
            fill='white'
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

                logo_center_x = image_w / 2
                logo_center_y = height + self.us(90) - (image_h / 2)

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
            forecast = []
            for i in range(1, 3):  # skip today (index 0), take next 2 days
                try:
                    dt = datetime.strptime(daily['time'][i], '%Y-%m-%d')
                    day_name = dt.strftime('%a')
                except:
                    day_name = daily['time'][i]
                code = daily['weather_code'][i]
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

    def draw_weather(self, width, height):
        """Draw current temperature and forecast in top-left, cycling between them."""
        if not self.weather_data:
            return

        x_start = self.us(20, 10)
        y_start = self.us(100, 50)
        padding = self.us(12, 6)
        panel_w = self.us(340, 180)

        # Current temperature group
        temp_text = f"{self.weather_data['current_temp']}°C"
        icon_text = self.weather_data['current_icon']

        curr_x = x_start + padding
        curr_y = y_start + padding

        icon_size = self.fs(36, 18)
        self.canvas.create_text(
            curr_x, curr_y,
            text=icon_text,
            font=('Segoe UI Emoji', icon_size),
            fill='white',
            anchor='nw',
            tags='weather_current'
        )

        temp_size = self.fs(48, 24)
        self.canvas.create_text(
            curr_x + self.us(70, 36), curr_y,
            text=temp_text,
            font=('Arial', temp_size, 'bold'),
            fill='#ffffff',
            anchor='nw',
            tags='weather_current'
        )

        # Forecast group (same position, initially hidden)
        forecast = self.weather_data.get('forecast', [])
        if forecast:
            forecast_y = y_start + padding
            col_width = (panel_w - 2 * padding) / len(forecast)
            forecast_font = self.fs(30, 15)
            icon_font = self.fs(28, 14)

            for i, day in enumerate(forecast):
                cx = x_start + padding + col_width * i + col_width / 2

                self.canvas.create_text(
                    cx, forecast_y,
                    text=day['day'],
                    font=('Arial', forecast_font, 'bold'),
                    fill='#c0d0e8',
                    anchor='n',
                    tags='weather_forecast'
                )

                self.canvas.create_text(
                    cx, forecast_y + self.us(44, 22),
                    text=day['icon'],
                    font=('Segoe UI Emoji', icon_font),
                    fill='white',
                    anchor='n',
                    tags='weather_forecast'
                )

                self.canvas.create_text(
                    cx, forecast_y + self.us(96, 48),
                    text=f"{day['high']}° / {day['low']}°",
                    font=('Arial', self.fs(30, 15), 'bold'),
                    fill='#8aadcc',
                    anchor='n',
                    tags='weather_forecast'
                )

        # Set initial visibility based on current state
        if self._weather_show_forecast:
            self._set_weather_group_state('weather_current', 'hidden')
            self._set_weather_group_state('weather_forecast', 'normal')
        else:
            self._set_weather_group_state('weather_current', 'normal')
            self._set_weather_group_state('weather_forecast', 'hidden')

        # Start cycle timer
        self._start_weather_cycle()

    def _set_weather_group_state(self, tag, state):
        """Set all canvas items with given tag to state ('normal' or 'hidden')."""
        for item_id in self.canvas.find_withtag(tag):
            self.canvas.itemconfig(item_id, state=state)

    def _start_weather_cycle(self):
        """Start the weather display cycle timer."""
        if self._weather_cycle_after_id:
            try:
                self.root.after_cancel(self._weather_cycle_after_id)
            except:
                pass
        # Current temp shows for 15s, forecast for 5s
        delay = 5000 if self._weather_show_forecast else 15000
        self._weather_cycle_after_id = self.root.after(delay, self._weather_cycle_step)

    def _weather_cycle_step(self):
        """Fade out current weather group, fade in next."""
        try:
            self._weather_fade_out(step=0)
        except:
            pass

    def _weather_fade_out(self, step=0):
        """Fade out the currently visible group over several steps."""
        total_steps = 6
        if step < total_steps:
            # Gradually reduce visibility isn't possible with state alone,
            # so we do a quick hide after a short delay for a clean transition
            self.root.after(40, lambda: self._weather_fade_out(step + 1))
            return

        # Switch groups
        if self._weather_show_forecast:
            self._set_weather_group_state('weather_forecast', 'hidden')
            self._weather_show_forecast = False
            self._weather_fade_in('weather_current', step=0)
        else:
            self._set_weather_group_state('weather_current', 'hidden')
            self._weather_show_forecast = True
            self._weather_fade_in('weather_forecast', step=0)

    def _weather_fade_in(self, tag, step=0):
        """Fade in the new weather group."""
        total_steps = 6
        if step == 0:
            self._set_weather_group_state(tag, 'normal')
        if step < total_steps:
            self.root.after(40, lambda: self._weather_fade_in(tag, step + 1))
            return
        # Restart cycle
        self._start_weather_cycle()

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

        # Draw weather in top-left corner
        if self.show_weather and self.weather_data:
            self.draw_weather(width, height)
        
        # Define prayers to display
        prayers = [
            ('FAJR', 'Fajr', 'الفجر'),
            ('DHUHR', 'Duhr', 'الظهر'),
            ('ASR', 'Asr', 'العصر'),
            ('MAGHRIB', 'Maghrib', 'المغرب'),
            ('ISHA', 'Isha', 'العشاء')
        ]

        # Reset box shape tracking for current frame
        self.prayer_box_shape_ids = {}
        self.prayer_box_bounds = {}
        
        # Get current prayer
        current_prayer = self.get_current_prayer(prayers_data)
        self.last_rendered_current_prayer = current_prayer

        if self.get_theme_name() == 'elegent':
            self.draw_elegent_compact_prayer_table(width, height, prayers_data, prayers, current_prayer)
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
                announcement_ribbon_y = height - self.us(128, 80)

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

        self.canvas.create_text(col_name_x, table_y + (header_h / 2) + self.us(8, 4), text='SALAH', font=('Arial', self.fs(28, 14), 'bold'), fill=palette['title_text'])
        self.canvas.create_text(col_athan_x, table_y + (header_h / 2) + self.us(8, 4), text='ATHAN', font=('Arial', self.fs(28, 14), 'bold'), fill=palette['title_text'])
        self.canvas.create_text(col_iqamah_x, table_y + (header_h / 2) + self.us(8, 4), text='IQAMAH', font=('Arial', self.fs(28, 14), 'bold'), fill=palette['title_text'])

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
            row_shape_id = self.canvas.create_rectangle(
                row_x,
                y1,
                row_x + row_w,
                y2,
                fill='',
                outline=row_outline,
                width=self.us(2, 1)
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
            if key == 'Fajr':
                if athan_time != '--' and 'AM' not in athan_time and 'PM' not in athan_time:
                    athan_time = athan_time + ' AM'
                if iqamah_time != '--' and 'AM' not in iqamah_time and 'PM' not in iqamah_time:
                    iqamah_time = iqamah_time + ' AM'

            show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))
            if show_arabic_name:
                name_text = arabic
                name_font = ('Arial', self.fs(30, 15), 'bold')
            else:
                name_text = display_name
                name_font = ('Arial', self.fs(30, 15), 'bold')

            self.canvas.create_text(col_name_x, y1 + (row_h / 2), text=name_text, font=name_font, fill=palette['title_text'])
            self.draw_time_text_with_meridiem(col_athan_x, y1 + (row_h / 2), athan_time, main_size=self.fs(36, 18), suffix_size=self.fs(18, 9), color=palette['athan_text'])
            self.draw_time_text_with_meridiem(col_iqamah_x, y1 + (row_h / 2), iqamah_time, main_size=self.fs(36, 18), suffix_size=self.fs(18, 9), color=palette['iqamah_text'])
    
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
                'radius': corner_radius
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
        show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))
        if show_arabic_name:
            name_text = arabic
            name_font = ('Arial', self.fs(42, 21), 'bold')
        else:
            name_text = name
            name_font = ('Arial', self.fs(42, 21), 'bold')
        self.canvas.create_text(
            x + width/2, y + self.us(42, 20),
            text=name_text,
            font=name_font,
            fill=palette['title_text']
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
            self.canvas.itemconfigure(notice_bg, state=ribbon_state, tags=('prayer_change_ribbon',))

            center_x = x + (width / 2)
            line1_y = y + (height * 0.18)
            iqamah_label_y = y + (height * 0.36)
            line2_y = y + (height * 0.56)
            line3_y = y + (height * 0.82)

            # Line 1: Prayer name
            self.canvas.create_text(
                center_x, line1_y,
                text=name.upper(),
                font=('Arial', self.fs(46, 23), 'bold'),
                fill='black',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 1b: "Iqamah" label
            self.canvas.create_text(
                center_x, iqamah_label_y,
                text='Iqamah',
                font=('Arial', self.fs(30, 15), 'bold'),
                fill='#2E7D32',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 2: New time with smaller AM/PM suffix (matching main prayer time style)
            self.draw_time_text_with_meridiem(
                center_x, line2_y,
                tomorrow_iqamah,
                main_size=self.fs(54, 27),
                suffix_size=self.fs(24, 12),
                color='#ff0000',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 3: Tomorrow
            self.canvas.create_text(
                center_x, line3_y,
                text='TOMORROW',
                font=('Arial', self.fs(34, 17), 'bold'),
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
        for prayer_key, shape_id in self.prayer_box_shape_ids.items():
            try:
                if prayer_key == blinking_prayer:
                    if blink_visible:
                        self.update_prayer_box_alpha_fill(prayer_key, palette['card_current_fill'], palette['card_current_outline'], 4)
                    else:
                        self.update_prayer_box_alpha_fill(prayer_key, palette['card_fill'], palette['card_outline'], 3)
                elif prayer_key == current_prayer:
                    self.update_prayer_box_alpha_fill(prayer_key, palette['card_current_fill'], palette['card_current_outline'], 4)
                else:
                    self.update_prayer_box_alpha_fill(prayer_key, palette['card_fill'], palette['card_outline'], 3)
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

    def update_prayer_box_alpha_fill(self, prayer_key, fill_color, outline_color=None, outline_width=0):
        """Update alpha fill+outline image in-place for a prayer box (no z-order change)."""
        style = self.prayer_box_fill_styles.get(prayer_key)
        if not style:
            return

        old_id = self.prayer_box_fill_ids.get(prayer_key)
        if not old_id:
            return

        w = max(1, int(round(style['width'])))
        h = max(1, int(round(style['height'])))
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
            outline_rgba = (or_, og, ob, 255)
            if rad > 0:
                draw.rounded_rectangle((0, 0, w - 1, h - 1), radius=rad, fill=None, outline=outline_rgba, width=ow)
            else:
                draw.rectangle((0, 0, w - 1, h - 1), fill=None, outline=outline_rgba, width=ow)

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
            'radius': corner_radius
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
            'radius': corner_radius
        }
        
        # Rotating Shrouq name (English/Arabic)
        show_arabic_name = bool(getattr(self, 'salah_names_show_arabic', False))
        if show_arabic_name:
            title_text = 'الشروق'
            title_font = ('Arial', self.fs(42, 21), 'bold')
        else:
            title_text = 'SHROUQ'
            title_font = ('Arial', self.fs(42, 21), 'bold')
        self.canvas.create_text(
            x + width/2, y + self.us(42, 20),
            text=title_text,
            font=title_font,
            fill=palette['title_text']
        )
        
        # Draw sunrise time
        self.draw_time_text_with_meridiem(
            x + width/2, y + self.us(113, 50),
            sunrise_time,
            main_size=self.fs(54, 26),
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
        parts = normalized_text.rsplit(' ', 1)

        if len(parts) == 2 and parts[1].upper() in ('AM', 'PM'):
            main_text = parts[0]
            suffix_text = f" {parts[1].upper()}"

            main_font = ('Arial', main_size, 'bold')
            suffix_font = ('Arial', suffix_size, 'bold')

            main_width = tkfont.Font(font=main_font).measure(main_text)
            suffix_width = tkfont.Font(font=suffix_font).measure(suffix_text)
            total_width = main_width + suffix_width
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
                font=('Arial', main_size, 'bold'),
                fill=color,
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
        panel_y1 = self.jummah_box_y + self.us(30, 15)
        line_center_y = panel_y1 + (panel_height / 2)

        # Move current time noticeably higher relative to the lower prayer row.
        current_time_y = self.jummah_box_y + self.jummah_box_h - self.us(20, 10)
        outline_step = self.us(3, 2)
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
        display_data = self.get_next_line_display_data(prayers_data)
        prefix_text = display_data['prefix_text']
        name_text = display_data['name_text']
        in_text = display_data['in_text']
        countdown_text = display_data['countdown_text']
        rtl_mode = bool(display_data.get('rtl', False))

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
        panel_x1 = x - (panel_width / 2)

        self.next_prayer_panel_id = self.draw_rounded_rectangle(
            panel_x1, panel_y1, panel_width, panel_height, self.next_prayer_panel_radius,
            fill=palette['next_panel_fill'], outline=palette['next_panel_outline'], outline_width=3
        )
        left_x = x - (total_width / 2)

        self.next_prayer_line_x = x
        self.next_prayer_line_y = line_center_y
        self.next_prayer_panel_width = panel_width
        self.next_prayer_panel_bounds = (panel_x1, panel_y1, panel_width, panel_height)
        self.next_prayer_static_width = panel_width
        self._next_prayer_last_text_parts = (prefix_text, name_text, in_text)
        self._next_prayer_last_widths = (prefix_width, name_width, in_width, countdown_width)
        if rtl_mode:
            right_x = x + (total_width / 2)
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

        self.draw_outlined_text(
            x, date_block_y,
            text=f"{day_text} | {hijri_text} | {miladi_text}",
            font=date_font,
            fill='white',
            outline='black',
            outline_px=self.us(3, 2),
            anchor='n'
        )

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
        """Switch language instantly with a single clean redraw."""
        target_show_arabic = bool(target_show_arabic)
        self.salah_name_transition_target_arabic = target_show_arabic
        self.salah_names_show_arabic = target_show_arabic
        self._last_salah_name_arabic_state = target_show_arabic

        if self.salah_name_transition_after_id is not None:
            try:
                self.root.after_cancel(self.salah_name_transition_after_id)
            except:
                pass
            self.salah_name_transition_after_id = None

        self.salah_name_transition_active = False
        self.salah_name_transition_progress = 1.0
        if not self.iqamah_overlay_visible:
            self.redraw_full_display()

    def _tick_salah_name_transition(self):
        """Advance Arabic reveal progress and request redraws."""
        step = self.salah_name_transition_tick_ms / max(1, self.salah_name_transition_duration_ms)
        self.salah_name_transition_progress = min(1.0, self.salah_name_transition_progress + step)

        if not self.iqamah_overlay_visible:
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
            self.redraw_full_display()

    def update_salah_name_rotation_state(self):
        """Show Arabic prayer names briefly on a configurable cadence, otherwise default to English."""
        try:
            change_every_seconds = int(self.config.get('arabicchangeevery', 30))
            change_every_seconds = max(1, change_every_seconds)
        except:
            change_every_seconds = 30

        try:
            arabic_duration_seconds = int(self.config.get('arabicnameduration', 5))
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
        """Schedule ribbon visibility cycle (15s ON, 15s OFF)"""
        self.update_ribbon_cycle()
    
    def update_ribbon_cycle(self):
        """Update prayer-change ribbon visibility (15s ON, 15s OFF) without redraw."""
        try:
            self.ribbon_cycle_counter = (self.ribbon_cycle_counter + 1) % 30
            self.ribbon_visible = (self.ribbon_cycle_counter < 15)

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
                    (change_item['prefix'], 'black'),
                    (change_item['new_time'], '#d32f2f'),
                    (change_item['suffix'], 'black')
                ]

                for segment_text, segment_color in segments:
                    text_id = self.canvas.create_text(
                        x + current_x, y + height/2,
                        text=segment_text,
                        font=('Arial', self.fs(40, 14), 'bold'),
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
            self.yellow_ribbon_total_width = (width - self.yellow_ribbon_x_positions[0] if self.yellow_ribbon_x_positions else 0)
            if self.yellow_ribbon_text_ids:
                last_item = self.yellow_ribbon_text_ids[-1]
                self.yellow_ribbon_total_width = self.yellow_ribbon_x_positions[-1] + last_item[3] + self.us(80, 24)

            # Keep existing scroll offset so redraws don't visibly restart the ticker.
            if not hasattr(self, 'yellow_ribbon_x_pos'):
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
                    # Move all text objects left
                    self.yellow_ribbon_x_pos -= 7  # Match announcement scroll speed
                    
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
                    if self.yellow_ribbon_x_pos < -self.yellow_ribbon_total_width:
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
        pass


if __name__ == '__main__':
    main()
