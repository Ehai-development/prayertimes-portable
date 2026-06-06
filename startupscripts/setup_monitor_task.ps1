# Prayer Time Display Monitor - Setup Script (Hidden)
# Registers a scheduled task that runs monitor_app.ps1 without showing any console window.

param(
    [switch]$SkipElevation = $false
)

$isAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole([Security.Principal.WindowsBuiltInRole] "Administrator")

if (-not $isAdmin -and -not $SkipElevation) {
    Write-Host "Administrator privileges are required. Attempting elevation..."
    Start-Process powershell.exe -Verb RunAs -ArgumentList "-NoProfile -ExecutionPolicy Bypass -File `"$PSCommandPath`" -SkipElevation" -Wait
    exit
}

$taskName = "PrayerTime App Monitor"
$legacyTaskName = "Prayer Time Display Monitor"
$scriptPath = "C:\portable\startupscripts\monitor_app.ps1"
$launcherPath = "C:\portable\startupscripts\run_monitor_hidden.vbs"

if (-not (Test-Path $scriptPath)) {
    Write-Host "ERROR: Monitor script not found: $scriptPath" -ForegroundColor Red
    exit 1
}

if (-not (Test-Path $launcherPath)) {
    Write-Host "ERROR: Hidden launcher not found: $launcherPath" -ForegroundColor Red
    exit 1
}

$existingTask = Get-ScheduledTask -TaskName $taskName -ErrorAction SilentlyContinue
if ($existingTask) {
    Unregister-ScheduledTask -TaskName $taskName -Confirm:$false -ErrorAction SilentlyContinue
    Start-Sleep -Seconds 1
}

$legacyTask = Get-ScheduledTask -TaskName $legacyTaskName -ErrorAction SilentlyContinue
if ($legacyTask) {
    Unregister-ScheduledTask -TaskName $legacyTaskName -Confirm:$false -ErrorAction SilentlyContinue
    Start-Sleep -Seconds 1
}

try {
    $action = New-ScheduledTaskAction -Execute "wscript.exe" -Argument "//B //Nologo `"$launcherPath`""

    $minuteStart = (Get-Date).AddMinutes(1)
    $trigger = New-ScheduledTaskTrigger -Once -At $minuteStart `
        -RepetitionInterval (New-TimeSpan -Minutes 1) `
        -RepetitionDuration (New-TimeSpan -Days 365)

    $triggerList = @($trigger)
    if ($isAdmin) {
        $loginTrigger = New-ScheduledTaskTrigger -AtLogOn -User $env:USERNAME
        $startupTrigger = New-ScheduledTaskTrigger -AtStartup
        $triggerList += @($loginTrigger, $startupTrigger)
    }

    $settings = New-ScheduledTaskSettingsSet `
        -AllowStartIfOnBatteries `
        -DontStopIfGoingOnBatteries `
        -StartWhenAvailable `
        -Hidden

    # Use current user so spawned app appears on desktop, but keep task hidden.
    if ($isAdmin) {
        $principal = New-ScheduledTaskPrincipal -UserId $env:USERNAME `
            -LogonType Interactive `
            -RunLevel Highest
    } else {
        $principal = New-ScheduledTaskPrincipal -UserId $env:USERNAME `
            -LogonType Interactive `
            -RunLevel Limited
    }

    Register-ScheduledTask -TaskName $taskName -Action $action -Trigger $triggerList -Settings $settings -Principal $principal -Force -ErrorAction Stop | Out-Null

    Start-ScheduledTask -TaskName $taskName -ErrorAction SilentlyContinue

    Write-Host "Task created successfully: $taskName" -ForegroundColor Green
    Write-Host "Launcher: $launcherPath"
    Write-Host "Script:   $scriptPath"
    Write-Host "Mode:     Hidden (no command prompt/PowerShell popup)"
}
catch {
    Write-Host "ERROR creating task: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}
