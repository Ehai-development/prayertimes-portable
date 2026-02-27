# Prayer Time Display App Monitor
# Checks if the app is running every minute and restarts it if needed

$APP_NAME = "PrayerTimeDisplay"
$APP_EXE = "C:\portable\standalone\PrayerTimeDisplay.exe"
$LOG_FILE = "C:\portable\startupscript\app_monitor.log"

# Function to write to log
function Write-Log {
    param([string]$Message)
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "$timestamp - $Message"
    Add-Content -Path $LOG_FILE -Value $logMessage
    Write-Host $logMessage
}

# Ensure log file exists
if (-not (Test-Path $LOG_FILE)) {
    New-Item -Path $LOG_FILE -ItemType File | Out-Null
}

# Check if app is running
$appProcess = Get-Process -Name $APP_NAME -ErrorAction SilentlyContinue

if ($appProcess) {
    Write-Log "✓ $APP_NAME is running (PID: $($appProcess.Id))"
} else {
    Write-Log "✗ $APP_NAME not found. Starting now..."
    
    # Verify executable exists
    if (Test-Path $APP_EXE) {
        try {
            # Set working directory to portable root so app can find config/data/images
            $workingDir = Split-Path -Parent $APP_EXE
            $workingDir = Split-Path -Parent $workingDir
            
            # Try different launch methods
            Write-Log "  Attempting launch from: $workingDir"
            Write-Log "  EXE: $APP_EXE"
            Write-Log "  EXE exists: $(Test-Path $APP_EXE)"
            Write-Log "  EXE size: $((Get-Item $APP_EXE).Length) bytes"
            
            # Method 1: Direct Start-Process (handles fullscreen app better)
            $proc = Start-Process -FilePath $APP_EXE -WorkingDirectory $workingDir -PassThru -ErrorAction Stop
            Write-Log "✓ $APP_NAME started (PID: $($proc.Id)) from $workingDir"
            
            # Give it a moment to appear
            Start-Sleep -Milliseconds 500
            
            # Check if it's still running
            if (-not $proc.HasExited) {
                Write-Log "✓ $APP_NAME is still running after launch"
            } else {
                Write-Log "⚠ $APP_NAME exited immediately (exit code: $($proc.ExitCode))"
            }
        } catch {
            Write-Log "✗ Failed to start $APP_NAME : $_"
            Write-Log "  Error type: $($_.Exception.GetType().Name)"
            Write-Log "  Error details: $($_.Exception.Message)"
        }
    } else {
        Write-Log "✗ Executable not found at: $APP_EXE"
    }
}

# Keep last 500 lines of log (cleanup)
$logLines = @(Get-Content $LOG_FILE)
if ($logLines.Count -gt 500) {
    $logLines[-500..-1] | Set-Content $LOG_FILE
}
