# Prayer Time Display - Auto-Restart Monitor Setup

## INITIAL SETUP (Run Once)

1. **Open Command Prompt as Administrator:**
   - Press `Win + R`
   - Type: `cmd`
   - Press `Ctrl+Shift+Enter` (or right-click and select "Run as administrator")

2. **Navigate to the folder:**
   ```
   cd C:\portable\startupscripts
   ```

3. **Run the setup:**
   ```
   setup_monitor_task.bat
   ```

4. **Verify it worked:**
   ```
   tasklist /v | find "Prayer"
   ```
   You should see "Prayer Time Display Monitor" in the list.

---

## HOW IT WORKS

Once installed, the monitor will:
- Check if `PrayerTimeDisplay.exe` is running **every minute**
- **Automatically restart** the app if it crashes or is closed
- Run in the background with **no command prompt / PowerShell popup**
- Log all activity to `C:\portable\startupscripts\app_monitor.log`

---

## TESTING

1. Close `PrayerTimeDisplay.exe` manually
2. Wait up to 1 minute
3. The app should automatically restart
4. Check the log file to confirm:
   ```
   type C:\portable\startupscripts\app_monitor.log
   ```

---

## TROUBLESHOOTING

**Q: Task isn't working**
A: This usually means the setup script wasn't run as Administrator. Try again:
   - Command Prompt → Right-click → "Run as administrator"
   - Then execute: `cd C:\portable\startupscripts && setup_monitor_task.bat`

**Q: App still isn't restarting**
A: Check the log file for errors:
   ```
   type C:\portable\startupscripts\app_monitor.log
   ```

**Q: Want to remove the auto-restart?**
A: Run as administrator:
   ```
   cd C:\portable\startupscripts
   remove_monitor_task.bat
   ```

---

## FILES

- `monitor_app.ps1` - The monitoring script (checks and restarts the app)
- `setup_monitor_task.bat` - Installs the monitor (run as admin)
- `remove_monitor_task.bat` - Uninstalls the monitor (run as admin)
- `app_monitor.log` - Log file showing all activity
