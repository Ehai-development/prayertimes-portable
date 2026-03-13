@echo off
REM Remove Prayer Time Display Monitor Task
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

echo Attempting to delete scheduled task...
echo Task Name: Prayer Time Display Monitor
echo.

schtasks /delete /tn "Prayer Time Display Monitor" /f

if errorlevel 1 (
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
echo The "Prayer Time Display Monitor" scheduled task
echo has been removed from Windows Task Scheduler.
echo.
echo The app will no longer auto-restart if it crashes.
echo.
pause
