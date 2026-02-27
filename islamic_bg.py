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
from PIL import Image, ImageTk

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

        self.logo_base_image = None
        self.logo_image_path = None
        
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
        
        # Tracking for prayer time changes (tomorrow vs today)
        self.changing_prayers = {}  # {prayer_name: {today: time, tomorrow: time}}
        self.announcement_scroll_complete = False
        
        # Red ribbon visibility cycle (15 sec ON, 15 sec OFF)
        self.ribbon_cycle_counter = 0  # 0-29 seconds
        self.ribbon_visible = True  # Start visible
        
        # Tracking for upcoming prayer time changes (3+ days ahead)
        self.upcoming_changes = {}  # {prayer_name: {change_date: date, new_time: time, old_time: time}}
        self.upcoming_change_alerts = {}  # {prayer_name: display_info} for yellow ribbon
        
        # Tracking for yellow ribbon scrolling animation
        self.yellow_ribbon_text_ids = []  # List of text object IDs for yellow ribbon
        self.yellow_ribbon_x_positions = []  # Starting x position of each item
        self.yellow_ribbon_total_width = 0  # Total width of all changes text
        self.yellow_ribbon_x_pos = 0  # Current x position for scrolling
        self.yellow_ribbon_x = 0  # Yellow ribbon left position
        self.yellow_ribbon_y = 0  # Yellow ribbon top position
        self.yellow_ribbon_width = 0  # Yellow ribbon width
        self.yellow_ribbon_height = 0  # Yellow ribbon height
        self.announcement_tick_ms = 100
        self.yellow_ribbon_tick_ms = 100
        
        # Jummah time (loaded from CSV or config/jummah.txt)
        self.jummah_time = None

        # Test mode indicator canvas IDs (updated in-place)
        self.test_mode_box_id = None
        self.test_mode_label_id = None
        self.test_mode_info_id = None
        
        # Load prayer times AFTER initializing tracking
        try:
            print("[STARTUP] Loading configuration...", flush=True)
            self.load_config()
            print("[STARTUP] Loading prayer times...", flush=True)
            self.load_prayer_times()
            print("[STARTUP] Loading Jummah time...", flush=True)
            self.load_jummah_time()
            print("[STARTUP] Loading announcements...", flush=True)
            self.load_announcements()
            
            # Check for prayer changes early so toggle starts with data ready
            print("[STARTUP] Checking for upcoming prayer changes...", flush=True)
            self.check_upcoming_changes()  # Check for changes 3+ days ahead (must be first)
            print("[STARTUP] Checking for tomorrow's prayer changes...", flush=True)
            self.check_prayer_changes()  # Check for tomorrow's changes (depends on upcoming_changes)
            
            # Start the countdown update loop
            print("[STARTUP] Starting update schedulers...", flush=True)
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
            print("[STARTUP] Drawing initial display...", flush=True)
            self.root.after(100, self.initial_draw)
            self.root.after(self.lantern_pulse_tick_ms, self.schedule_lantern_pulse_animation)
            self.root.after(self.star_twinkle_tick_ms, self.schedule_star_twinkle_animation)
        except Exception as e:
            print(f"[ERROR] Startup failed: {e}", flush=True)
            import traceback
            traceback.print_exc()
            import sys
            sys.exit(1)

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
                    print(f"[DATE] TEST MODE: Using mocked date {mocked_date} (System date: {datetime.now().date()})")
                    self._test_mode_date_logged = True
                return mocked_date
            except:
                if not self._test_mode_date_error_logged:
                    print(f"Invalid TEST_DATE format: {TEST_DATE}. Using system date.")
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
                    print(f"Invalid TEST_TIME format: {TEST_TIME}. Using system time.")
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
            print(f"[DATE] Day changed to {new_date}; refreshing display/data...")

            if self.iqamah_overlay_visible:
                self.hide_iqamah_overlay()

            self.load_prayer_times()
            self.load_announcements()
            self.check_upcoming_changes()
            self.check_prayer_changes()
            self.redraw_full_display()
        except Exception as e:
            print(f"ERROR in handle_date_rollover: {e}")
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
            print("[STARTUP] [OK] App startup complete - rendering background...")
            
            # Defer Islamic background generation to after window is visible
            self.root.after(100, self._generate_and_apply_background_deferred)
        except Exception as e:
            print(f"ERROR in initial_draw: {e}")
            import traceback
            traceback.print_exc()
    
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
            
            print("[STARTUP] Background rendering complete!")
        except Exception as e:
            print(f"ERROR in _generate_and_apply_background_deferred: {e}")
            import traceback
            traceback.print_exc()
        
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
            print(f"ERROR in _perform_resize_redraw: {e}")

    def redraw_full_display(self):
        """Redraw full canvas in correct z-order."""
        if self._is_full_redraw:
            return

        self._is_full_redraw = True
        try:
            self.canvas.delete('all')
            self.draw_islamic_background()
            self.draw_prayer_times()
            self.draw_test_mode_indicator()
        finally:
            self._is_full_redraw = False

    def schedule_lantern_pulse_animation(self):
        """Refresh Ramadan lanterns so they continuously dim/brighten."""
        try:
            if self.is_ramadan(self.get_current_date()) and not self.iqamah_overlay_visible and not self._is_full_redraw:
                self.update_lanterns_only()
        except Exception as e:
            print(f"ERROR in schedule_lantern_pulse_animation: {e}")
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
            print(f"ERROR in schedule_star_twinkle_animation: {e}")
        finally:
            try:
                self.root.after(self.star_twinkle_tick_ms, self.schedule_star_twinkle_animation)
            except:
                pass

    def update_lanterns_only(self):
        """Update only the lantern visuals without redrawing the entire display."""
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        if width <= 1 or height <= 1:
            return

        self.canvas.delete('animated_lanterns')

        lantern_top_y = height / 2 - self.us(380)
        lantern_size = self.us(120, 60)
        lantern_spacing = width / 5

        for i in [0, 3]:
            x = lantern_spacing * (i + 1)
            self.draw_ramadan_lantern(x, lantern_top_y, lantern_size, tags='animated_lanterns')

    def update_stars_only(self):
        """Update only star visuals with twinkling effect without redrawing entire display."""
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        if width <= 1 or height <= 1:
            return

        self.canvas.delete('animated_stars')

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

        current_date = self.get_current_date()
        if self.is_ramadan(current_date):
            self.draw_ramadan_background(width, height)
            return
        
        # Create gradient effect with overlapping rectangles
        gradient_steps = 50
        for i in range(gradient_steps):
            ratio = i / gradient_steps
            # Light blue gradient
            r = int(90 + (120 - 90) * ratio)
            g = int(120 + (150 - 120) * ratio)
            b = int(170 + (200 - 170) * ratio)
            color = f'#{r:02x}{g:02x}{b:02x}'
            
            y_pos = (height * i) / gradient_steps
            self.canvas.create_rectangle(
                0, y_pos, width, y_pos + height/gradient_steps + 2,
                fill=color, outline=''
            )
        
        # Draw Islamic 8-pointed star pattern
        # self.draw_star_pattern(width, height)  # Disabled
        
        # Draw crescent moons
        self.draw_crescents(width, height)
        
        # Draw 5-pointed stars of different sizes
        self.draw_five_pointed_stars(width, height)
        
        # Draw large decorative circles in background
        self.draw_background_ornaments(width, height)
        
        # Draw corner ornaments
        self.draw_corner_ornaments(width, height)

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
            (0.10, 'lantern', 0.090),
            (0.24, 'crescent', 0.040),
            (0.36, 'star', 0.030),
            (0.50, 'crescent', 0.048),
            (0.64, 'star', 0.030),
            (0.76, 'crescent', 0.040),
            (0.90, 'lantern', 0.090),
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
            print(f"Error loading config: {e}")
            self.config = {
                "data_file": "prayer_times.csv",
                "location": "MASJID AL-SALAM",
                "prayernow": 3
            }

        # Post-prayer overlay duration in minutes (configurable)
        try:
            prayernow_minutes = int(self.config.get('prayernow', 3))
            prayernow_minutes = max(0, prayernow_minutes)
        except:
            prayernow_minutes = 3
        self.config['prayernow'] = prayernow_minutes
        self.iqamah_post_duration_seconds = prayernow_minutes * 60
        
        # Load location/address from address.txt if available
        address_path = config_dir / 'address.txt'
        try:
            if address_path.exists():
                with open(address_path, 'r', encoding='utf-8') as f:
                    address = f.read().strip()
                    if address:
                        self.config['location'] = address
        except Exception as e:
            print(f"Error loading address: {e}")
        
        # Load masjid name from masjid.txt if available
        masjid_path = config_dir / 'masjid.txt'
        try:
            if masjid_path.exists():
                with open(masjid_path, 'r', encoding='utf-8') as f:
                    masjid_name = f.read().strip()
                    if masjid_name:
                        self.config['masjid_name'] = masjid_name
        except Exception as e:
            print(f"Error loading masjid name: {e}")

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
    
    def draw_background_ornaments(self, width, height):
        """Draw large decorative circular patterns in background"""
        # Draw large semi-transparent geometric patterns
        positions = [
            (width * 0.2, height * 0.3, 150),
            (width * 0.8, height * 0.3, 150),
            (width * 0.2, height * 0.7, 150),
            (width * 0.8, height * 0.7, 150),
        ]
        
        for x, y, radius in positions:
            # Draw concentric circles
            for i in range(3):
                r = radius - (i * 25)
                self.canvas.create_oval(
                    x - r, y - r, x + r, y + r,
                    outline='#7896c8',
                    width=2,
                    stipple='gray12'
                )
            
            # Draw radiating lines from center
            num_lines = 16
            for i in range(num_lines):
                angle = (i * 2 * math.pi / num_lines)
                x1 = x + 40 * math.cos(angle)
                y1 = y + 40 * math.sin(angle)
                x2 = x + radius * math.cos(angle)
                y2 = y + radius * math.sin(angle)
                self.canvas.create_line(
                    x1, y1, x2, y2,
                    fill='#7896c8',
                    width=1,
                    stipple='gray12'
                )
    
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

            print(f"Loaded {base_count} base prayer entries from {base_csv_path.name}")
            print(f"[RAMADAN] Applied {ramadan_overrides} Ramadan overrides from {ramadan_csv_path.name}")
            print(f"Total active prayer entries: {len(self.prayer_data)}")

        except Exception as e:
            print(f"Error loading prayer times: {e}")
            self.prayer_data = {}
    
    def load_jummah_time(self):
        """Load Jummah time from today's CSV DuhrIqama or from config/jummah.txt"""
        try:
            # Try to get today's Duhr Iqama time from CSV (used for Friday Jummah)
            today_date_str = self.get_current_date().strftime('%Y-%m-%d')
            prayers_data = self.prayer_data.get(today_date_str, {})
            duhr_iqama = prayers_data.get('DuhrIqama', '').strip()
            
            if duhr_iqama and duhr_iqama != '--':
                # Use DuhrIqama from CSV as Jummah time
                self.jummah_time = self.parse_time(duhr_iqama)
                print(f"[JUMMAH] Using Jummah time from CSV: {duhr_iqama}")
            else:
                # Fall back to config/jummah.txt
                config_dir = self.get_config_dir()
                jummah_file = config_dir / 'jummah.txt'
                
                if not jummah_file.exists():
                    # Create default file
                    jummah_file.write_text('1:30 PM', encoding='utf-8')
                    print("[JUMMAH] Created config/jummah.txt with default time 1:30 PM")
                
                jummah_time_str = jummah_file.read_text(encoding='utf-8').strip()
                self.jummah_time = self.parse_time(jummah_time_str)
                print(f"[JUMMAH] Using Jummah time from config/jummah.txt: {jummah_time_str}")
                
        except Exception as e:
            print(f"[ERROR] Failed to load Jummah time: {e}")
            # Default fallback
            self.jummah_time = self.parse_time('1:30 PM')
            print("[JUMMAH] Using default Jummah time: 1:30 PM")
    
    def load_announcements(self):
        """Load announcements from announcements.txt (always)."""
        # Check if current date (which might be TEST_DATE) is in Ramadan
        current_date = self.get_current_date()
        is_ramadan_period = self.is_ramadan(current_date)

        config_dir = self.get_config_dir()
        announcements_path = config_dir / 'announcements.txt'
        print(f"[ANNOUNCEMENTS] Loading from {announcements_path}")
        if announcements_path.exists():
            print(f"[ANNOUNCEMENTS] Last modified: {datetime.fromtimestamp(announcements_path.stat().st_mtime)}")
        
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
                    default_msg = "Welcome to Ramadan!" if is_ramadan_period else "Welcome to Rose City Islamic Centre"
                    self.announcements = [(default_msg, 'white')]
                    
                print(f"Loaded {len(self.announcements)} announcements with colors from {announcements_path.name}")
                for text, color in self.announcements:
                    print(f"  - '{text}' (color: {color})")
                    
        except Exception as e:
            print(f"Error loading announcements: {e}")
            default_msg = "Welcome to Ramadan!" if is_ramadan_period else "Welcome to Rose City Islamic Centre"
            self.announcements = [(default_msg, 'white')]
        
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
            if change_info.get('days_until') == 1:  # Changes tomorrow (1 day away) - show red ribbon today
                # Store the change info for red ribbon display
                self.changing_prayers[prayer] = {
                    'today': change_info.get('old_time', '--'),
                    'tomorrow': change_info.get('new_time', '--'),
                    'today_iqama': change_info.get('old_time', '--'),
                    'tomorrow_iqama': change_info.get('new_time', '--')
                }
    
    def check_upcoming_changes(self):
        """Check for upcoming prayer time changes by reading Notes column in CSV"""
        self.upcoming_changes = {}
        today = self.get_current_date()
        
        # Look for ANNOUNCEMENT dates (changes happen next day or on that day)
        # To find changes 1-3 days away, check announcements 0-3 days ahead
        for days_ahead in range(0, 4):  # Check 0, 1, 2, 3 days ahead (for changes up to 3 days away)
            check_date = (today + timedelta(days=days_ahead)).strftime('%Y-%m-%d')
            check_data = self.prayer_data.get(check_date, {})
            
            if not check_data:
                continue
            
            # Read the Notes column to find documented changes (announced on this date)
            notes = check_data.get('Notes', '')
            if notes and ('Iqama time changes' in notes or '->' in notes):
                
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
                    
                    for prayer in prayers_list:
                        # Check if this prayer is mentioned in the Notes (indicating a change)
                        if prayer in notes:
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
            jummah_time = self.jummah_time or self.parse_time(prayers_data.get('DuhrIqama', ''))

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
            jummah_time = self.jummah_time or self.parse_time(prayers_data.get('DuhrIqama', ''))
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
            current_prayer = self.get_current_prayer(prayers_data)

            if current_prayer:
                is_friday = (self.get_current_date().weekday() == 4)
                current_athan = self.parse_time(prayers_data.get(f'{current_prayer}Athan', ''))
                current_iqamah = self.parse_time(prayers_data.get(f'{current_prayer}Iqama', ''))

                if current_athan and current_iqamah and current_athan <= now < current_iqamah:
                    if current_prayer == 'Duhr' and is_friday:
                        return {
                            'prefix_text': '',
                            'name_text': 'JUMMAH KHUTBAH',
                            'in_text': ' IN ',
                            'countdown_text': self.get_countdown(current_iqamah)
                        }

                    return {
                        'prefix_text': '',
                        'name_text': current_prayer.upper(),
                        'in_text': ' IQAMAH IN ',
                        'countdown_text': self.get_countdown(current_iqamah)
                    }

            next_prayer_name, next_athan = self.get_next_prayer(prayers_data)
            self.next_prayer_athan_time = next_athan
            return {
                'prefix_text': 'NEXT PRAYER: ',
                'name_text': (next_prayer_name or '---').upper(),
                'in_text': ' IN ',
                'countdown_text': self.get_countdown(next_athan)
            }
        except:
            return {
                'prefix_text': 'NEXT PRAYER: ',
                'name_text': '---',
                'in_text': ' IN ',
                'countdown_text': '--:--:--'
            }
    
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

                    if current_prayer_now != self.last_rendered_current_prayer:
                        self.last_rendered_current_prayer = current_prayer_now
                        self.update_prayer_box_highlight_states(current_prayer_now)
                    elif not self.iqamah_overlay_visible:
                        self.update_prayer_box_highlight_states(current_prayer_now)

                    display_data = self.get_next_line_display_data(prayers_data)
                    prefix_text = display_data['prefix_text']
                    name_text = display_data['name_text']
                    in_text = display_data['in_text']
                    countdown_text = display_data['countdown_text']

                    self.canvas.itemconfig(self.next_prayer_prefix_text_id, text=prefix_text, fill='black')
                    self.canvas.itemconfig(self.next_prayer_name_text_id, text=name_text, fill='#d32f2f')
                    self.canvas.itemconfig(self.next_prayer_in_text_id, text=in_text, fill='black')
                    self.canvas.itemconfig(self.countdown_text_id, text=countdown_text, fill='#2E7D32')

                    if self.next_prayer_line_x is not None and self.next_prayer_line_y is not None:
                        text_parts = (prefix_text, name_text, in_text)
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

                        # Keep panel width stable during per-second countdown ticks.
                        base_panel_width = self.next_prayer_static_width if self.next_prayer_static_width else max(260, total_width + (self.next_prayer_panel_padding_x * 2))
                        if self.next_prayer_max_panel_width:
                            panel_width = min(base_panel_width, self.next_prayer_max_panel_width)
                        else:
                            panel_width = base_panel_width
                        panel_x1 = self.next_prayer_line_x - (panel_width / 2)
                        panel_y1 = self.next_prayer_line_y - (self.next_prayer_panel_height / 2)

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

                        self.canvas.coords(self.next_prayer_prefix_text_id, left_x, self.next_prayer_line_y)
                        self.canvas.coords(self.next_prayer_name_text_id, left_x + prefix_width, self.next_prayer_line_y)
                        self.canvas.coords(self.next_prayer_in_text_id, left_x + prefix_width + name_width, self.next_prayer_line_y)
                        self.canvas.coords(self.countdown_text_id, left_x + prefix_width + name_width + in_width, self.next_prayer_line_y)
                except:
                    pass
        except Exception as e:
            print(f"ERROR in update_countdown: {e}")
        
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
                    print(f"[PERF] update_countdown slow: {elapsed_ms:.1f}ms")
    
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

                if not athan_time or not iqamah_time:
                    continue

                athan_dt = datetime.combine(mocked_date, athan_time)
                iqamah_dt = datetime.combine(mocked_date, iqamah_time)
                post_end_dt = iqamah_dt + timedelta(seconds=self.iqamah_post_duration_seconds)

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
                    # For Friday Jummah, just hide overlay if visible
                    if self.iqamah_overlay_visible:
                        self.hide_iqamah_overlay()
            else:
                if self.iqamah_overlay_visible:
                    self.hide_iqamah_overlay()
        
        except Exception as e:
            print(f"ERROR in check_iqamah_countdown: {e}")
            import traceback
            traceback.print_exc()
        
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
                    print(f"[PERF] check_iqamah_countdown slow: {elapsed_ms:.1f}ms")
    
    def show_iqamah_overlay(self):
        """Show the full-screen Iqamah countdown overlay"""
        try:
            width = self.canvas.winfo_width()
            height = self.canvas.winfo_height()
            
            # Full-screen overlay background
            overlay_bg = self.canvas.create_rectangle(
                0, 0, width, height,
                fill='#f2f2f2',
                outline='',
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(overlay_bg)

            line1_y = height * 0.31
            countdown_y = line1_y + self.us(185, 105)
            notice_y = countdown_y + self.us(235, 130)
            icon_y = notice_y + self.us(175, 95)
            is_friday_khutbah = (self.current_prayer_name == 'Jummah' and self.get_current_date().weekday() == 4)
            prayer_line_text = f"{self.current_prayer_name.upper()} IQAMAH IN"
            instruction_line_text = 'Please put your cell phone on silent mode'
            instruction_font_size = self.fs(68, 32)

            if is_friday_khutbah:
                prayer_line_text = 'JUMMAH KHUTBAH IN'
                instruction_line_text = 'Talking is forbidden during Khutbahs'
                instruction_font_size = self.fs(74, 34)

            # Prayer line: PRAYERNAME IQAMAH IN (green)
            prayer_text = self.canvas.create_text(
                width / 2, line1_y,
                text=prayer_line_text,
                font=('Arial', self.fs(78, 34), 'bold'),
                fill='#2E7D32',
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(prayer_text)

            # Countdown time (will be updated every second)
            countdown = self.get_iqamah_countdown()
            countdown_text = self.canvas.create_text(
                width / 2, countdown_y,
                text=countdown,
                font=('Arial', self.fs(170, 72), 'bold'),
                fill='#d32f2f',
                tags=('iqamah_overlay', 'iqamah_countdown_time')
            )
            self.iqamah_overlay_ids.append(countdown_text)

            # Cell phone notice (black and bigger)
            instruction_text = self.canvas.create_text(
                width / 2, notice_y,
                text=instruction_line_text,
                font=('Arial', instruction_font_size, 'bold'),
                fill='black',
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(instruction_text)

            # Larger centered no-phone icon beneath the notice
            icon_ids = self.draw_no_phone_icon(width / 2, icon_y, size=self.us(240, 130), tags='iqamah_overlay')
            self.iqamah_overlay_ids.extend(icon_ids)
            
            # Raise overlay to top of canvas stacking order
            self.canvas.tag_raise('iqamah_overlay')
            
            self.iqamah_overlay_visible = True
            self.iqamah_overlay_mode = 'countdown'
            
        except Exception as e:
            print(f"ERROR in show_iqamah_overlay: {e}")
            import traceback
            traceback.print_exc()

    def show_post_iqamah_overlay(self):
        """Show post-iqamah overlay for 3 minutes with ayah and prayer notice."""
        try:
            self.clear_iqamah_overlay_items()
            width = self.canvas.winfo_width()
            height = self.canvas.winfo_height()

            overlay_bg = self.canvas.create_rectangle(
                0, 0, width, height,
                fill='#f2f2f2',
                outline='',
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(overlay_bg)

            ayah_y = height * 0.24
            notice_y = ayah_y + self.us(185, 105)
            icon_y = notice_y + self.us(220, 125)
            prayer_now_y = icon_y + self.us(230, 130)

            ayah_text = self.canvas.create_text(
                width / 2, ayah_y,
                text='إِنَّ الصَّلَاةَ كَانَتْ عَلَى الْمُؤْمِنِينَ كِتَابًا مَوْقُوتًا',
                font=('Arial', self.fs(74, 36), 'bold'),
                fill='#2E7D32',
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(ayah_text)

            instruction_text = self.canvas.create_text(
                width / 2, notice_y,
                text='Please put your cell phone on silent mode',
                font=('Arial', self.fs(62, 30), 'bold'),
                fill='black',
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(instruction_text)

            icon_ids = self.draw_no_phone_icon(width / 2, icon_y, size=self.us(240, 130), tags='iqamah_overlay')
            self.iqamah_overlay_ids.extend(icon_ids)

            prayer_now_text = self.canvas.create_text(
                width / 2, prayer_now_y,
                text='Prayer is now',
                font=('Arial', self.fs(92, 42), 'bold'),
                fill='#d32f2f',
                tags='iqamah_overlay'
            )
            self.iqamah_overlay_ids.append(prayer_now_text)

            # Raise overlay to top of canvas stacking order
            self.canvas.tag_raise('iqamah_overlay')

            self.iqamah_overlay_visible = True
            self.iqamah_overlay_mode = 'post'

        except Exception as e:
            print(f"ERROR in show_post_iqamah_overlay: {e}")
            import traceback
            traceback.print_exc()

    def clear_iqamah_overlay_items(self):
        """Delete overlay canvas items while preserving overlay state variables."""
        try:
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
            print(f"ERROR in hide_iqamah_overlay: {e}")

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

            # Find and update the countdown text element
            items = self.canvas.find_withtag('iqamah_countdown_time')
            if items:
                self.canvas.itemconfig(items[0], text=countdown)
        except Exception as e:
            print(f"ERROR in update_iqamah_overlay_countdown: {e}")
    
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
            print(f"ERROR in get_iqamah_countdown: {e}")
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
        # Get masjid name and address from config
        masjid_name = self.config.get('masjid_name', 'MASJID')
        address = self.config.get('location', 'Address')

        # Draw logo in top-right corner
        self.draw_top_right_logo(width, height)
        
        # Draw masjid name (larger)
        self.draw_outlined_text(
            width / 2, self.us(35),
            text=masjid_name,
            font=('Arial', self.fs(44, 18), 'bold'),
            fill='white'
        )
        
        # Draw address (smaller)
        self.canvas.create_text(
            width / 2, self.us(100),
            text=address,
            font=('Arial', self.fs(18, 10)),
            fill='white'
        )
        
        # Draw decorative line below title
        line_width = self.us(400)
        self.canvas.create_line(
            width/2 - line_width/2, self.us(120),
            width/2 + line_width/2, self.us(120),
            fill='#2a5a8f',
            width=self.us(2)
        )

    def draw_top_right_logo(self, width, height):
        """Draw the configured logo image at the top-right and top-left corners."""
        try:
            target_size = (self.us(300), self.us(200))
            images_dir = Path(__file__).parent / 'images'
            primary_path = images_dir / 'main.png'
            fallback_path = images_dir / 'main.jpg'
            image_path = primary_path if primary_path.exists() else fallback_path

            if image_path.exists():
                if self.logo_base_image is None or self.logo_image_path != str(image_path) or self.logo_image_size != target_size:
                    with Image.open(image_path) as img:
                        self.logo_base_image = img.convert('RGBA').resize(target_size, Image.LANCZOS)
                        self.logo_image_size = target_size
                        self.logo_image_path = str(image_path)

                if self.logo_base_image is not None:
                    self.logo_image_tk = ImageTk.PhotoImage(self.logo_base_image)

            if self.logo_image_tk is not None:
                left_image_x = self.us(24)
                image_y = self.us(18)
                image_w, image_h = target_size

                left_center_x = left_image_x + (image_w / 2)
                left_center_y = image_y + (image_h / 2)
                right_center_x = width - self.us(24) - (image_w / 2)
                right_center_y = image_y + (image_h / 2)

                self.canvas.create_image(
                    left_center_x,
                    left_center_y,
                    image=self.logo_image_tk,
                    anchor='center'
                )
                self.canvas.create_image(
                    right_center_x,
                    right_center_y,
                    image=self.logo_image_tk,
                    anchor='center'
                )

                if self.is_ramadan(self.get_current_date()):
                    calligraphy_candidates = ['Segoe Script', 'Lucida Handwriting', 'Brush Script MT']
                    calligraphy_font = next(
                        (font_name for font_name in calligraphy_candidates if font_name in tkfont.families()),
                        'Arial'
                    )
                    text_y = image_y + image_h + self.us(18, 8)
                    left_text_x = left_center_x
                    right_text_x = right_center_x

                    self.draw_outlined_text(
                        left_text_x,
                        text_y,
                        text='Ramadhan Mubarak',
                        font=(calligraphy_font, self.fs(20, 10), 'bold'),
                        fill='#d4af37',
                        outline='black',
                        outline_px=self.us(2, 1),
                        anchor='center'
                    )
                    self.draw_outlined_text(
                        right_text_x,
                        text_y,
                        text='Ramadhan Mubarak',
                        font=(calligraphy_font, self.fs(20, 10), 'bold'),
                        fill='#d4af37',
                        outline='black',
                        outline_px=self.us(2, 1),
                        anchor='center'
                    )
        except Exception as e:
            print(f"ERROR in draw_top_right_logo: {e}")

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
        """Draw current date and day at top left in white"""
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
            self.us(60), self.us(45),
            text=day_name,
            font=('Arial', self.fs(34, 15), 'bold'),
            fill='white',
            anchor='nw'
        )
        
        # Draw Miladi date
        self.draw_outlined_text(
            self.us(60), self.us(105),
            text=date_str,
            font=('Arial', self.fs(22, 11)),
            fill='white',
            anchor='nw'
        )
        
        # Draw Hijri date
        self.draw_outlined_text(
            self.us(60), self.us(140),
            text=hijri_str,
            font=('Arial', self.fs(22, 11)),
            fill='white',
            anchor='nw'
        )
    
    def get_hijri_month_name(self, month):
        """Get Hijri month name"""
        hijri_months = [
            'Muharram', 'Safar', 'Rabil Al-Awwal', 'Rabil Al-Thani',
            'Jumada Al-Awwal', 'Jumada Al-Thani', 'Rajab', 'Sha\'ban',
            'Ramadan', 'Shawwal', 'Dhu Al-Qi\'dah', 'Dhu Al-Hijjah'
        ]
        return hijri_months[month - 1] if 1 <= month <= 12 else 'Unknown'
    
    def draw_quran_verse(self, width, height):
        """Draw Quranic verse above prayer times with translation"""
        # Arabic verse: "Verily, as-Salat (the prayer) is enjoined on the believers at fixed hours" (An-Nisa 4:103)
        verse = "إِنَّ الصَّلَاةَ كَانَتْ عَلَى الْمُؤْمِنِينَ كِتَابًا مَوْقُوتًا"
        translation = "Prayer has been decreed upon the believers at specific times."
        
        # Display the verse in the middle of the page, above prayer times
        # Calculate position - moved higher on the page
        verse_y = height / 2 - self.us(324)
        
        # Draw semi-transparent background box for verse
        box_height = self.us(100)
        box_y1 = verse_y - box_height / 2
        box_y2 = verse_y + box_height / 2
        
        self.canvas.create_rectangle(
            0, box_y1, width, box_y2,
            fill='#1a3a5a',
            outline='',
            stipple='gray12'
        )
        
        # Draw white rounded box behind Arabic verse text
        arabic_font_size = self.fs(54, 20)
        arabic_font_obj = tkfont.Font(family='Arial', size=arabic_font_size, weight='bold')
        arabic_text_w = arabic_font_obj.measure(verse)
        arabic_box_w = min(width - self.us(120, 50), arabic_text_w + self.us(90, 40))
        arabic_box_h = self.us(88, 44)

        self.draw_rounded_rectangle(
            (width / 2) - (arabic_box_w / 2),
            verse_y - self.us(72, 36),
            arabic_box_w,
            arabic_box_h,
            self.us(20, 10),
            fill='white',
            outline='#8b5a2b',
            outline_width=self.us(2, 1)
        )

        # Draw the Arabic verse text
        verse_text_y = verse_y - self.us(30, 15)
        self.draw_outlined_text(
            width / 2, verse_text_y,
            text=verse,
            font=('Arial', arabic_font_size, 'bold'),
            fill='#d4af37',  # Gold color for Arabic text
            outline='black',
            outline_px=self.us(3, 1),
            anchor='center',
            justify='center'
        )
        
        # Draw the English translation text (increased spacing from Arabic line)
        translation_y = verse_y + self.us(36)
        self.draw_outlined_text(
            width / 2, translation_y,
            text=translation,
            font=('Arial', self.fs(30, 14)),
            fill='#ffffff',  # White color for translation
            outline='',
            outline_px=0,
            anchor='center',
            justify='center'
        )
        
        # Draw the date below the translation
        try:
            current_date = self.get_current_date()
            day_name = current_date.strftime('%A')
            hijri_date = Gregorian(current_date.year, current_date.month, current_date.day).to_hijri()
            miladi_date = current_date.strftime('%d %B %Y')
            
            hijri_date_str = f"{hijri_date.day} {self._get_hijri_month_name(hijri_date.month)} {hijri_date.year}"
            date_text = f"{day_name}, {hijri_date_str} || {miladi_date}"
            
            date_y = translation_y + self.us(52)
            self.draw_outlined_text(
                width / 2, date_y,
                text=date_text,
                font=('Arial', self.fs(30, 14), 'bold'),
                fill='#ffffff',  # White color for date
                outline='',
                outline_px=0,
                anchor='center',
                justify='center'
            )
        except Exception as e:
            print(f"ERROR drawing date: {e}")
    
    def draw_prayer_times(self):
        """Draw prayer time boxes with error handling"""
        try:
            return self._draw_prayer_times_impl()
        except Exception as e:
            print(f"ERROR in draw_prayer_times: {e}")
            import traceback
            traceback.print_exc()
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
            ('FAJR', 'Fajr', 'الفجر'),
            ('DHUHR', 'Duhr', 'الظهر'),
            ('ASR', 'Asr', 'العصر'),
            ('MAGHRIB', 'Maghrib', 'المغرب'),
            ('ISHA', 'Isha', 'العشاء')
        ]

        # Reset box shape tracking for current frame
        self.prayer_box_shape_ids = {}
        
        # Get current prayer
        current_prayer = self.get_current_prayer(prayers_data)
        self.last_rendered_current_prayer = current_prayer
        
        # Calculate box dimensions - all same size
        box_width = self.us(320, 190)
        box_height = self.us(230, 140)
        lower_row_box_height = max(self.us(190, 120), box_height - self.us(40, 20))
        spacing = self.us(30, 15)
        
        # Calculate total width
        total_width = (box_width * 5) + (spacing * 4)
        
        start_x = (width - total_width) / 2
        center_y = (height / 2) + self.us(40, 20)
        
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
            
            # Draw Jummah box moved to below Isha (was at top left)
            if idx == 4:
                jummah_box_x = x
                jummah_box_y = y + box_h + lower_row_offset
                jummah_box_h = lower_row_box_height
                is_jummah_current = (current_prayer == 'Jummah')
                jummah_shape_id = self.draw_khutbah_box(jummah_box_x, jummah_box_y, box_width, jummah_box_h, is_current=is_jummah_current)
                if jummah_shape_id:
                    self.prayer_box_shape_ids['Jummah'] = jummah_shape_id
                
                # Check if there are changes within 2 days (including day of change)
                has_upcoming_changes = False
                if self.upcoming_changes:
                    for prayer_key, info in self.upcoming_changes.items():
                        days_until = info.get('days_until', 0)
                        # Show yellow ribbon from 2 days before until midnight on day of change
                        if 0 <= days_until <= 2:
                            has_upcoming_changes = True
                            break
                
                ribbon_y = y + box_h + lower_row_offset + lower_row_box_height + self.us(15, 8)
                
                # Draw yellow ribbon if there are changes within the next 2 days
                if has_upcoming_changes:
                    yellow_ribbon_height = self.us(70, 40)
                    self.draw_upcoming_changes_ribbon(0, ribbon_y, width, yellow_ribbon_height)
                    ribbon_y = ribbon_y + yellow_ribbon_height + self.us(5, 3)
                
                # Draw announcement ribbon
                self.draw_announcement_ribbon(0, ribbon_y, width, self.us(86, 52))
            
            x_offset += box_w + spacing

        # Draw standalone current time centered between Next Prayer and Jummah boxes
        if next_prayer_box_x is not None and jummah_box_x is not None:
            next_center_x = next_prayer_box_x + (box_width / 2)
            jummah_center_x = jummah_box_x + (box_width / 2)

            middle_gap_width = max(0, jummah_box_x - (next_prayer_box_x + box_width))
            self.next_prayer_max_panel_width = max(self.us(220, 130), middle_gap_width - self.us(18, 10))

            current_time_x = (next_center_x + jummah_center_x) / 2

            # Keep the next-prayer panel bottom aligned with Jummah box bottom.
            # draw_current_time_display uses panel_y1 = y + 24 and panel_height = 72.
            next_prayer_panel_offset_y = self.us(36, 16)
            next_prayer_panel_height = self.next_prayer_panel_height
            jummah_bottom_y = jummah_box_y + jummah_box_h
            current_time_y = jummah_bottom_y - (next_prayer_panel_offset_y + next_prayer_panel_height) - self.us(0, 0)

            self.draw_current_time_display(current_time_x, current_time_y, next_prayer_name_for_display)

        self.draw_build_info(width, height)
    
    def draw_prayer_box(self, x, y, width, height, name, arabic, athan, iqamah, is_current=False, show_tomorrow_iqamah=False, prayer_key=None, tomorrow_iqamah=None):
        """Draw a single prayer time box with rounded corners"""
        # Different colors for current prayer
        if is_current:
            fill_color = '#ffb74d'  # Orange highlight (more visible on bright displays)
            outline_color = '#f57c00'  # Orange
            outline_w = 4
        else:
            fill_color = 'white'
            outline_color = '#2a5a8f'
            outline_w = 3
        
        # Draw rounded rectangle background
        box_shape_id = self.draw_rounded_rectangle(x, y, width, height, self.us(40, 22), fill=fill_color, outline=outline_color, outline_width=outline_w)
        
        # Prayer name
        name_y = y + self.us(35, 18)
        self.canvas.create_text(
            x + width/2, name_y,
            text=name,
            font=('Arial', self.fs(36, 18), 'bold'),
            fill='#1a3a5f'
        )
        
        # Arabic name
        arabic_y = name_y + self.us(30, 14)
        self.canvas.create_text(
            x + width/2, arabic_y,
            text=arabic,
            font=('Arial', self.fs(24, 12)),
            fill='#4a6a8f'
        )
        
        # Athan time
        athan_y = arabic_y + self.us(48, 22)
        # Removed "ATHAN" label
        self.draw_time_text_with_meridiem(
            x + width/2, athan_y,
            athan,
            main_size=self.fs(60, 30),
            suffix_size=self.fs(24, 12),
            color='#1a3a5f'
        )
        
        # Iqamah time
        iqamah_y = athan_y + self.us(72, 34)
        
        # Display center iqamah time (always show current time until midnight)
        # Removed "IQAMAH" label
        
        self.draw_time_text_with_meridiem(
            x + width/2, iqamah_y,
            iqamah,
            main_size=self.fs(60, 30),
            suffix_size=self.fs(24, 12),
            color='#2a8a5f'
        )
        
        # Draw full-box change notice if prayer changes tomorrow (1 day before change)
        if show_tomorrow_iqamah and tomorrow_iqamah:
            ribbon_state = 'normal' if self.ribbon_visible else 'hidden'

            notice_pad = self.us(8, 4)
            notice_x1 = x + notice_pad
            notice_y1 = y + notice_pad
            notice_x2 = x + width - notice_pad
            notice_y2 = y + height - notice_pad

            # Full notice background covering prayer-box content area
            self.canvas.create_rectangle(
                notice_x1, notice_y1, notice_x2, notice_y2,
                fill='white',
                outline='',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Red bordered card
            self.canvas.create_rectangle(
                notice_x1, notice_y1, notice_x2, notice_y2,
                fill='',
                outline='#ff0000',
                width=self.us(2, 1),
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            center_x = x + (width / 2)
            line1_y = y + (height * 0.24)
            line2_y = y + (height * 0.44)
            line3_y = y + (height * 0.63)
            line4_y = y + (height * 0.81)

            # Line 1: Prayer name
            self.canvas.create_text(
                center_x, line1_y,
                text=name,
                font=('Arial', self.fs(30, 15), 'bold'),
                fill='black',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 2: Iqamah label
            self.canvas.create_text(
                center_x, line2_y,
                text='IQAMAH CHANGES TO',
                font=('Arial', self.fs(20, 10), 'bold'),
                fill='black',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 3: New time
            self.canvas.create_text(
                center_x, line3_y,
                text=tomorrow_iqamah,
                font=('Arial', self.fs(38, 18), 'bold'),
                fill='#ff0000',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )

            # Line 4: Starts tomorrow
            self.canvas.create_text(
                center_x, line4_y,
                text='STARTS TOMORROW',
                font=('Arial', self.fs(20, 10), 'bold'),
                fill='#ff0000',
                tags=('prayer_change_ribbon',),
                state=ribbon_state
            )
        
        # Check for upcoming changes (3+ days ahead) - display as yellow news ribbon
        # This will be displayed separately in the main ribbon area, not in the prayer box
        # So we just remove this block completely from here
        return box_shape_id

    def update_prayer_box_highlight_states(self, current_prayer):
        """Update only prayer box highlight styles without full-canvas redraw."""
        for prayer_key, shape_id in self.prayer_box_shape_ids.items():
            try:
                if prayer_key == current_prayer:
                    self.canvas.itemconfig(shape_id, fill='#ffb74d', outline='#f57c00', width=4)
                else:
                    self.canvas.itemconfig(shape_id, fill='white', outline='#2a5a8f', width=3)
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
    
    def draw_khutbah_box(self, x, y, width, height, is_current=False):
        """Draw Khutbah (Friday Sermon) box"""
        # Draw rounded rectangle background with highlight if current
        if is_current:
            fill_color = '#ffb74d'
            outline_color = '#f57c00'
            outline_w = 4
        else:
            fill_color = 'white'
            outline_color = '#2a5a8f'
            outline_w = 3
        box_shape_id = self.draw_rounded_rectangle(x, y, width, height, self.us(40, 22), fill=fill_color, outline=outline_color, outline_width=outline_w)
        
        # Draw Jummah text
        self.canvas.create_text(
            x + width/2, y + self.us(20, 10),
            text='JUMMAH',
            font=('Arial', self.fs(24, 12), 'bold'),
            fill='#1a3a5f'
        )
        
        # Draw Khutbah text
        self.canvas.create_text(
            x + width/2, y + self.us(50, 22),
            text='KHUTBAH',
            font=('Arial', self.fs(18, 10)),
            fill='#4a6a8f'
        )
        
        # Draw time - use loaded Jummah time
        jummah_time_str = '1:30 PM'  # Default
        if self.jummah_time:
            jummah_time_str = self.jummah_time.strftime('%I:%M %p').lstrip('0')
        
        self.draw_time_text_with_meridiem(
            x + width/2, y + self.us(98, 42),
            jummah_time_str,
            main_size=self.fs(54, 26),
            suffix_size=self.fs(24, 12),
            color='#1a3a5f'
        )
        
        # Draw "ALL YEAR LONG" in red
        self.canvas.create_text(
            x + width/2, y + self.us(158, 72),
            text='ALL YEAR LONG',
            font=('Arial', self.fs(24, 12), 'bold'),
            fill='#d32f2f'
        )
        
        return box_shape_id
    
    def draw_shouruq_box(self, x, y, width, height, sunrise_time, is_current=False):
        """Draw Shouruq (Sunrise) box"""
        if is_current:
            fill_color = '#ffb74d'
            outline_color = '#f57c00'
            outline_w = 4
        else:
            fill_color = 'white'
            outline_color = '#2a5a8f'
            outline_w = 3

        # Draw rounded rectangle background
        box_shape_id = self.draw_rounded_rectangle(x, y, width, height, self.us(40, 22), fill=fill_color, outline=outline_color, outline_width=outline_w)
        
        # Draw Shrouq text (match regular prayer box styling)
        self.canvas.create_text(
            x + width/2, y + self.us(35, 18),
            text='SHROUQ',
            font=('Arial', self.fs(32, 16), 'bold'),
            fill='#1a3a5f'
        )
        
        # Draw Arabic name
        self.canvas.create_text(
            x + width/2, y + self.us(65, 28),
            text='الشروق',
            font=('Arial', self.fs(24, 12)),
            fill='#4a6a8f'
        )
        
        # Draw sunrise time
        self.draw_time_text_with_meridiem(
            x + width/2, y + self.us(113, 50),
            sunrise_time,
            main_size=self.fs(54, 26),
            suffix_size=self.fs(24, 12),
            color='#1a3a5f'
        )

        # +10 minutes note at the bottom
        self.canvas.create_text(
            x + width/2, y + height - self.us(25, 12),
            text='+ 10 MINUTES',
            font=('Arial', self.fs(26, 14), 'bold'),
            fill='green'
        )

        return box_shape_id

    def draw_time_text_with_meridiem(self, x, y, time_text, main_size=36, suffix_size=20, color='#1a3a5f'):
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
                anchor='w'
            )
            self.canvas.create_text(
                left_x + main_width, y,
                text=suffix_text,
                font=suffix_font,
                fill=color,
                anchor='w'
            )
        else:
            self.canvas.create_text(
                x, y,
                text=normalized_text,
                font=('Arial', main_size, 'bold'),
                fill=color
            )
    
    def draw_next_prayer_box(self, x, y, width, height, prayer_name, athan_time):
        """Legacy placement anchor (visual next-prayer content is now standalone)"""
        # Keep anchor values for layout/reference; countdown is drawn in draw_current_time_display
        self.countdown_y = y + 62
        self.countdown_x = x + width/2

    def draw_current_time_display(self, x, y, next_prayer_name):
        """Draw standalone current time display with seconds and next prayer below"""
        # Live time text (updated every second in update_countdown)
        current_time_text = self.get_current_time().strftime('%I:%M:%S %p')

        # Place current time under the date line section (newer layout request),
        # while keeping the next-prayer panel at its existing lower position.
        current_time_y = (self.canvas.winfo_height() / 2) - self.us(148, 70)

        outline_step = self.us(2, 1)
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
                font=('Arial', self.fs(75, 36), 'bold'),
                fill='black'
            )
            self.current_time_outline_ids.append(outline_id)

        self.current_time_text_id = self.canvas.create_text(
            x, current_time_y,
            text=current_time_text,
            font=('Arial', self.fs(75, 36), 'bold'),
            fill='white'
        )

        # White rounded box like prayer boxes for next prayer info
        panel_height = self.next_prayer_panel_height
        panel_y1 = y + self.us(36, 16)
        line_center_y = panel_y1 + (panel_height / 2)

        # Next prayer line in one row with split colors
        prayers_data = self.get_today_prayers()
        display_data = self.get_next_line_display_data(prayers_data)
        prefix_text = display_data['prefix_text']
        name_text = display_data['name_text']
        in_text = display_data['in_text']
        countdown_text = display_data['countdown_text']

        line_size = int(self.next_prayer_line_font.cget('size'))
        prefix_size = int(self.next_prayer_prefix_font.cget('size'))
        min_line_size = max(18, self.fs(28, 14))
        min_prefix_size = max(14, self.fs(22, 12))

        while True:
            line_font_obj = tkfont.Font(family='Arial', size=line_size, weight='bold')
            prefix_font_obj = tkfont.Font(family='Arial', size=prefix_size, weight='bold')

            prefix_width = prefix_font_obj.measure(prefix_text)
            name_width = line_font_obj.measure(name_text)
            in_width = line_font_obj.measure(in_text)
            countdown_width = line_font_obj.measure('88:88:88')
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
            fill='white', outline='#2a5a8f', outline_width=3
        )
        left_x = x - (total_width / 2)

        self.next_prayer_line_x = x
        self.next_prayer_line_y = line_center_y
        self.next_prayer_panel_width = panel_width
        self.next_prayer_static_width = panel_width
        self._next_prayer_last_text_parts = (prefix_text, name_text, in_text)
        self._next_prayer_last_widths = (prefix_width, name_width, in_width, countdown_width)

        self.next_prayer_prefix_text_id = self.canvas.create_text(
            left_x, line_center_y,
            text=prefix_text,
            font=prefix_font,
            fill='black',
            anchor='w'
        )
        self.next_prayer_name_text_id = self.canvas.create_text(
            left_x + prefix_width, line_center_y,
            text=name_text,
            font=line_font,
            fill='#d32f2f',
            anchor='w'
        )
        self.next_prayer_in_text_id = self.canvas.create_text(
            left_x + prefix_width + name_width, line_center_y,
            text=in_text,
            font=line_font,
            fill='black',
            anchor='w'
        )
        self.countdown_text_id = self.canvas.create_text(
            left_x + prefix_width + name_width + in_width, line_center_y,
            text=countdown_text,
            font=line_font,
            fill='#2E7D32',
            anchor='w'
        )

    def draw_build_info(self, width, height):
        """Draw app build date/time in the bottom-left corner."""
        self.build_info_text_id = self.canvas.create_text(
            self.us(14, 8),
            height - self.us(10, 6),
            text=self.build_info_text,
            font=('Arial', self.fs(18, 10)),
            fill='white',
            anchor='sw'
        )
    
    def schedule_prayer_time_toggle(self):
        """Schedule the prayer time toggle every 15 minutes"""
        self.update_prayer_time_toggle()
    
    def update_prayer_time_toggle(self):
        """Toggle between today's and tomorrow's Iqamah times - DISABLED"""
        # This function is now disabled because we use automatic switching
        # based on whether the next prayer has started (more intuitive behavior)
        # The show_tomorrow_time values are now set in check_prayer_changes()
        
        try:
            # Still increment counter for compatibility
            self.tomorrow_time_toggle_counter += 1
        except Exception as e:
            print(f"ERROR in update_prayer_time_toggle: {e}")
        
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
            print(f"ERROR in update_ribbon_cycle: {e}")
        
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
            
            print("CSV reloaded - prayer/announcement data updated")
        except Exception as e:
            print(f"ERROR in update_csv_reload: {e}")
        
        # Schedule next reload in 60 seconds (60000ms)
        try:
            self.root.after(60000, self.update_csv_reload)
        except:
            pass
    
    def draw_upcoming_changes_ribbon(self, x, y, width, height):
        """Draw a yellow news ribbon for upcoming prayer time changes"""
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
        current_x = self.us(20, 8)  # Start visible inside the ribbon
        
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
            
            # Calculate total width for looping
            self.yellow_ribbon_total_width = current_x + self.us(100, 30)
            # Initialize scroll position - starts visible
            self.yellow_ribbon_x_pos = 0
        # Note: If no changes, the yellow ribbon won't be drawn at all
    
    def draw_announcement_ribbon(self, x, y, width, height):
        """Draw a red announcement ribbon for news ticker with all announcements"""
        # Draw red rectangle background
        self.canvas.create_rectangle(
            x, y, x + width, y + height,
            fill='#d32f2f',  # Red
            outline='#b71c1c',  # Darker red border
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
                
            print(f"Created {len(self.announcement_text_ids)} announcement text objects")
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
    
    def schedule_announcement_update(self):
        """Schedule announcement updates"""
        self.update_announcement()
    
    def update_announcement(self):
        """Update the scrolling announcement text - scroll all at once"""
        _t0 = datetime.now() if ENABLE_PERF_TRACE else None
        try:
            if self.announcement_text_ids and len(self.announcement_text_ids) > 0:
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
                        # Reset to start (all announcements will loop from right)
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
                    print(f"[PERF] update_announcement slow: {elapsed_ms:.1f}ms")
    
    def update_yellow_ribbon(self):
        """Update the scrolling yellow ribbon text - scroll continuously"""
        _t0 = datetime.now() if ENABLE_PERF_TRACE else None
        try:
            if self.yellow_ribbon_text_ids and len(self.yellow_ribbon_text_ids) > 0:
                try:
                    # Move all text objects left
                    self.yellow_ribbon_x_pos -= 3  # Scroll speed
                    
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
                        # Reset to start (text will loop from right)
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
                    print(f"[PERF] update_yellow_ribbon slow: {elapsed_ms:.1f}ms")
    
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
        print(f"ERROR: {e}")
        import traceback
        traceback.print_exc()


if __name__ == '__main__':
    main()
