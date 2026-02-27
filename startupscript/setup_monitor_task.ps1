# Prayer Time Display Monitor - Setup Script
# This script registers the app monitor as a Windows Scheduled Task
# It will attempt to auto-elevate to administrator if needed

param(
    [switch]$SkipElevation = $false
)

# Check if running as admin
$isAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole([Security.Principal.WindowsBuiltInRole] "Administrator")

if (-not $isAdmin -and -not $SkipElevation) {
    Write-Host "This script requires Administrator privileges."
    Write-Host "Attempting to elevate..."
    Start-Process powershell.exe -Verb RunAs -ArgumentList "-NoProfile -ExecutionPolicy Bypass -File `"$PSCommandPath`" -SkipElevation" -Wait
    exit
}

Write-Host ""
Write-Host "╔════════════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║  Prayer Time Display - Monitor Setup              ║" -ForegroundColor Green
Write-Host "╚════════════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""

$taskName = "Prayer Time Display Monitor"
$scriptPath = "C:\portable\startupscript\monitor_app.ps1"

# Verify script exists
if (-not (Test-Path $scriptPath)) {
    Write-Host "ERROR: Monitor script not found at: $scriptPath" -ForegroundColor Red
    pause
    exit 1
}

# Delete existing task if it exists
Write-Host "Checking for existing task..." -ForegroundColor Cyan
$existingTask = Get-ScheduledTask -TaskName $taskName -ErrorAction SilentlyContinue
if ($existingTask) {
    Write-Host "Removing old task..." -ForegroundColor Yellow
    Unregister-ScheduledTask -TaskName $taskName -Confirm:$false -ErrorAction SilentlyContinue
    Start-Sleep -Seconds 1
}

# Create the scheduled task
Write-Host "Creating new scheduled task..." -ForegroundColor Cyan
Write-Host "  Task Name: $taskName"
Write-Host "  Script: $scriptPath"
Write-Host "  Frequency: Every 1 minute"
Write-Host ""

try {
    $action = New-ScheduledTaskAction -Execute "powershell.exe" `
        -Argument "-NoProfile -ExecutionPolicy Bypass -File `"$scriptPath`""
    
    $trigger = New-ScheduledTaskTrigger -Once -At (Get-Date) `
        -RepetitionInterval (New-TimeSpan -Minutes 1) `
        -RepetitionDuration (New-TimeSpan -Days 365)
    
    $settings = New-ScheduledTaskSettingsSet `
        -AllowStartIfOnBatteries `
        -DontStopIfGoingOnBatteries `
        -StartWhenAvailable
    
    $principal = New-ScheduledTaskPrincipal -UserId "SYSTEM" `
        -LogonType ServiceAccount -RunLevel Highest
    
    $task = Register-ScheduledTask `
        -TaskName $taskName `
        -Action $action `
        -Trigger $trigger `
        -Settings $settings `
        -Principal $principal `
        -Force
    
    if ($task) {
        Write-Host "✓ Task created successfully!" -ForegroundColor Green
        Write-Host ""
        Write-Host "╔════════════════════════════════════════════════════╗" -ForegroundColor Green
        Write-Host "║        Setup Complete!                            ║" -ForegroundColor Green
        Write-Host "╚════════════════════════════════════════════════════╝" -ForegroundColor Green
        Write-Host ""
        Write-Host "The monitor will:" -ForegroundColor Cyan
        Write-Host "  • Check if PrayerTimeDisplay.exe is running every minute"
        Write-Host "  • Start the app automatically if it stops/crashes"
        Write-Host "  • Log all activity to: C:\portable\startupscript\app_monitor.log"
        Write-Host ""
        Write-Host "To verify it's working:" -ForegroundColor Yellow
        Write-Host "  1. Close the PrayerTimeDisplay.exe app"
        Write-Host "  2. Wait up to 1 minute"
        Write-Host "  3. It should restart automatically"
        Write-Host ""
        Write-Host "To view the log:" -ForegroundColor Yellow
        Write-Host "  powershell -Command Get-Content 'C:\portable\startupscript\app_monitor.log' -Tail 20"
        Write-Host ""
    } else {
        Write-Host "ERROR: Failed to create task!" -ForegroundColor Red
        pause
        exit 1
    }
} catch {
    Write-Host "ERROR: $_" -ForegroundColor Red
    pause
    exit 1
}

pause
