@echo off
REM Setup Prayer Time Display Monitor Task
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

echo [1/2] Deleting any existing task...
schtasks /delete /tn "Prayer Time Display Monitor" /f >nul 2>&1
echo √ Old task cleaned up
echo.

echo [2/2] Creating new scheduled task...
echo This will run C:\AI\prayertime\monitor_app.ps1 every minute
echo.

schtasks /create ^
    /tn "Prayer Time Display Monitor" ^
    /tr "powershell.exe -NoProfile -ExecutionPolicy Bypass -File C:\portable\startupscript\monitor_app.ps1" ^
    /sc minute ^
    /mo 1 ^
    /f

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
echo Task Name: Prayer Time Display Monitor
echo Script:    C:\AI\prayertime\monitor_app.ps1
echo Frequency: Every 1 minute
echo Status:    Running as SYSTEM with High privileges
echo Log File:  C:\AI\prayertime\app_monitor.log
echo.
echo The monitor will:
echo   • Check if PrayerTimeDisplay.exe is running every minute
echo   • Start the app automatically if it stops
echo   • Write status to app_monitor.log
echo.
echo To view the log file:
echo   type C:\AI\prayertime\app_monitor.log
echo.
echo To disable the task:
echo   schtasks /delete /tn "Prayer Time Display Monitor"
echo.
pause
