@echo off
REM Remove PrayerTime App Monitor Task
REM Run this as Administrator to delete the scheduled task

echo.
echo ╔════════════════════════════════════════════════════╗
echo ║  Prayer Time Display - Remove Monitor Task        ║
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

echo Attempting to delete scheduled tasks...
echo Task Name: PrayerTime App Monitor
echo.

schtasks /delete /tn "PrayerTime App Monitor" /f >nul 2>&1
set "DELETED=0"
if %errorlevel% equ 0 set "DELETED=1"

schtasks /delete /tn "Prayer Time Display Monitor" /f >nul 2>&1
if %errorlevel% equ 0 set "DELETED=1"

if "%DELETED%"=="0" (
    echo.
    echo Task may not exist or deletion failed.
    echo Run this as Administrator if you see permission errors.
    pause
    exit /b 1
)

echo.
echo ╔════════════════════════════════════════════════════╗
echo ║        Task Deleted Successfully!                 ║
echo ╚════════════════════════════════════════════════════╝
echo.
echo The monitor scheduled task has been removed from Windows Task Scheduler.
echo.
echo The app will no longer auto-restart if it crashes.
echo.
pause
