@echo off
REM Setup PrayerTime App Monitor Task
REM Run this as Administrator

echo.
echo ╔════════════════════════════════════════════════════╗
echo ║  Prayer Time Display - Auto-Monitor Setup         ║
echo ║  NOTE: Run this as Administrator                  ║
echo ╚════════════════════════════════════════════════════╝
echo.

REM Check for admin privileges
net session >nul 2>&1
if %errorlevel% neq 0 (
    echo.
    echo ERROR: This script requires Administrator privileges!
    echo.
    echo Please:
    echo 1. Right-click this file
    echo 2. Select "Run as Administrator"
    echo.
    pause
    exit /b 1
)

echo [1/1] Installing monitor task via PowerShell setup script...
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0setup_monitor_task.ps1" -SkipElevation

if errorlevel 1 (
    echo.
    echo ERROR: Failed to create task!
    pause
    exit /b 1
)

echo.
echo ╔════════════════════════════════════════════════════╗
echo ║        Task Setup Complete!                        ║
echo ╚════════════════════════════════════════════════════╝
echo.
echo The following has been configured:
echo.
echo Task Name: PrayerTime App Monitor
echo Launcher:  C:\portable\startupscripts\run_monitor_hidden.vbs
echo Script:    C:\portable\startupscripts\monitor_app.ps1
echo Frequency: Every 1 minute
echo Status:    Hidden (no command window)
echo Log File:  C:\portable\startupscripts\app_monitor.log
echo.
echo The monitor will:
echo   • Check if PrayerTimeDisplay.exe is running every minute
echo   • Start the app automatically if it stops
echo   • Write status to app_monitor.log
echo.
echo To view the log file:
echo   type C:\portable\startupscripts\app_monitor.log
echo.
echo To disable the task:
echo   schtasks /delete /tn "PrayerTime App Monitor"
echo.
pause
