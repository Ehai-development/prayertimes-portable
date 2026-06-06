# Prayer Time Display App Monitor + GitHub Portable Updater
# Checks every minute for changes under portable/ and downloads only changed files.

$APP_NAME = "PrayerTimeDisplay"
$APP_EXE = "C:\portable\standalone\PrayerTimeDisplay.exe"
$LOG_FILE = "C:\portable\startupscripts\app_monitor.log"

$GITHUB_OWNER = "Ehai-development"
$GITHUB_REPO = "prayertimes-portable"
$GITHUB_BRANCH = "main"
$REPO_CONTENT_PREFIX = ""
$USE_GITHUB_TOKEN = $false

Add-Type -AssemblyName System.Windows.Forms
Add-Type -AssemblyName Microsoft.VisualBasic

$PORTABLE_ROOT = Split-Path -Parent (Split-Path -Parent $APP_EXE)
$STATE_DIR = Join-Path $PORTABLE_ROOT ".update_state"
$LAST_SHA_FILE = Join-Path $STATE_DIR "portable_last_sha.txt"
$LAST_EXE_SHA_FILE = Join-Path $STATE_DIR "portable_exe_sha.txt"
$LAST_START_FILE = Join-Path $STATE_DIR "portable_last_start.txt"
$PORTABLE_EXE_RELATIVE_PATH = "standalone/PrayerTimeDisplay.exe"

function Write-Log {
    param([string]$Message)
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "$timestamp - $Message"
    Add-Content -Path $LOG_FILE -Value $logMessage
}

function Ensure-Setup {
    if (-not (Test-Path $LOG_FILE)) {
        New-Item -Path $LOG_FILE -ItemType File -Force | Out-Null
    }
    if (-not (Test-Path $STATE_DIR)) {
        New-Item -Path $STATE_DIR -ItemType Directory -Force | Out-Null
    }
}

function Is-AnotherMonitorInstanceRunning {
    try {
        $currentPid = $PID
        $processes = Get-CimInstance Win32_Process -ErrorAction Stop |
            Where-Object {
                $_.ProcessId -ne $currentPid -and
                $_.Name -match '^(powershell|pwsh)\.exe$' -and
                $_.CommandLine -and
                $_.CommandLine -match '(?i)monitor_app\.ps1'
            }

        return ($processes.Count -gt 0)
    } catch {
        return $false
    }
}

function Get-GitHubHeaders {
    $headers = @{
        "User-Agent" = "PrayerTimeMonitor"
        "Accept" = "application/vnd.github+json"
    }
    if ($USE_GITHUB_TOKEN) {
        $token = $env:GITHUB_TOKEN

        if (-not [string]::IsNullOrWhiteSpace($token)) {
            $headers["Authorization"] = "token $($token.Trim())"
        }
    }
    return $headers
}

function Is-NetworkUnavailableError {
    param([System.Exception]$Exception)

    if ($null -eq $Exception) {
        return $false
    }

    $current = $Exception
    while ($null -ne $current) {
        if ($current -is [System.Net.WebException]) {
            switch ($current.Status) {
                NameResolutionFailure { return $true }
                ProxyNameResolutionFailure { return $true }
                ConnectFailure { return $true }
                Timeout { return $true }
                SendFailure { return $true }
                ReceiveFailure { return $true }
            }
        }

        $message = [string]$current.Message
        if ($message -match '(?i)(no such host is known|name or service not known|could not resolve|unable to connect|network is unreachable|connection.*(failed|refused|timed out)|temporarily unavailable)') {
            return $true
        }

        $current = $current.InnerException
    }

    return $false
}

function Get-PortableAppProcesses {
    return @(Get-Process -Name $APP_NAME -ErrorAction SilentlyContinue)
}

function Get-AppProcess {
    $portableProcesses = Get-PortableAppProcesses
    if ($portableProcesses.Count -gt 0) {
        return ($portableProcesses | Sort-Object ProcessId | Select-Object -First 1)
    }

    return $null
}

function Stop-App {
    $processes = Get-PortableAppProcesses
    if ($processes.Count -gt 0) {
        try {
            foreach ($p in $processes) {
                Stop-Process -Id $p.Id -Force -ErrorAction SilentlyContinue
            }
            Write-Log "Stopped $APP_NAME for update ($($processes.Count) process(es))"
            Start-Sleep -Milliseconds 800
        } catch {
            Write-Log "Failed to stop ${APP_NAME}: $($_.Exception.Message)"
        }
    }
}

function Start-App {
    if (-not (Test-Path $APP_EXE)) {
        Write-Log "Executable missing: $APP_EXE"
        return
    }

    $running = Get-PortableAppProcesses
    if ($running.Count -gt 0) {
        Write-Log "$APP_NAME already running ($($running.Count) process(es)); skipping start"
        return
    }

    try {
        $workingDir = Split-Path -Parent $APP_EXE
        $workingDir = Split-Path -Parent $workingDir
        $proc = Start-Process -FilePath $APP_EXE -WorkingDirectory $workingDir -PassThru -ErrorAction Stop
        Set-Content -Path $LAST_START_FILE -Value ((Get-Date).ToString("o")) -Encoding UTF8
        Write-Log "Started $APP_NAME (PID: $($proc.Id))"
    } catch {
        Write-Log "Failed to start ${APP_NAME}: $($_.Exception.Message)"
    }
}

function Was-AppStartedRecently {
    param([int]$WindowSeconds = 120)

    if (-not (Test-Path $LAST_START_FILE)) {
        return $false
    }

    try {
        $raw = (Get-Content -Path $LAST_START_FILE -ErrorAction Stop | Select-Object -First 1)
        if ([string]::IsNullOrWhiteSpace($raw)) {
            return $false
        }

        $lastStart = [DateTime]::Parse($raw, [System.Globalization.CultureInfo]::InvariantCulture, [System.Globalization.DateTimeStyles]::RoundtripKind)
        $elapsed = (Get-Date) - $lastStart
        return ($elapsed.TotalSeconds -lt $WindowSeconds)
    } catch {
        return $false
    }
}

function Ensure-AppFullscreen {
    param([System.Diagnostics.Process]$AppProcess)

    if ($null -eq $AppProcess) {
        return
    }

    if (-not ("Win32WindowApi" -as [type])) {
        Add-Type @"
using System;
using System.Runtime.InteropServices;

public static class Win32WindowApi {
    [StructLayout(LayoutKind.Sequential)]
    public struct RECT {
        public int Left;
        public int Top;
        public int Right;
        public int Bottom;
    }

    [DllImport("user32.dll")]
    public static extern bool GetWindowRect(IntPtr hWnd, out RECT lpRect);

    [DllImport("user32.dll")]
    public static extern bool SetForegroundWindow(IntPtr hWnd);

    [DllImport("user32.dll")]
    public static extern bool ShowWindowAsync(IntPtr hWnd, int nCmdShow);
}
"@
    }

    $AppProcess.Refresh()
    if ($AppProcess.MainWindowHandle -eq 0) {
        Write-Log "Fullscreen check skipped: no main window handle yet for PID $($AppProcess.Id)"
        return
    }

    $handle = $AppProcess.MainWindowHandle
    [Win32WindowApi]::ShowWindowAsync($handle, 9) | Out-Null
    [Win32WindowApi]::SetForegroundWindow($handle) | Out-Null

    $rect = New-Object Win32WindowApi+RECT
    if (-not [Win32WindowApi]::GetWindowRect($handle, [ref]$rect)) {
        Write-Log "Fullscreen check failed: unable to read window bounds for PID $($AppProcess.Id)"
        return
    }

    $screen = [System.Windows.Forms.Screen]::PrimaryScreen.Bounds
    $isFullscreen = (
        [Math]::Abs($rect.Left - $screen.Left) -le 2 -and
        [Math]::Abs($rect.Top - $screen.Top) -le 2 -and
        [Math]::Abs(($rect.Right - $rect.Left) - $screen.Width) -le 2 -and
        [Math]::Abs(($rect.Bottom - $rect.Top) - $screen.Height) -le 2
    )

    if (-not $isFullscreen) {
        [Microsoft.VisualBasic.Interaction]::AppActivate($AppProcess.Id) | Out-Null
        Start-Sleep -Milliseconds 150
        $wshell = New-Object -ComObject WScript.Shell
        $wshell.SendKeys('{F11}')
        Write-Log "Fullscreen enforcement: sent F11 to PID $($AppProcess.Id)"
    } else {
        Write-Log "Fullscreen enforcement: already fullscreen (PID: $($AppProcess.Id))"
    }
}

function Get-RemotePortableCommitSha {
    $uri = "https://api.github.com/repos/$GITHUB_OWNER/$GITHUB_REPO/branches/$GITHUB_BRANCH"
    $headers = Get-GitHubHeaders
    $response = Invoke-RestMethod -Uri $uri -Headers $headers -Method Get -ErrorAction Stop
    if ($response -and $response.commit -and $response.commit.sha) {
        return $response.commit.sha
    }
    return $null
}

function Get-ChangedPortableFiles {
    param(
        [string]$BaseSha,
        [string]$HeadSha
    )

    if ([string]::IsNullOrWhiteSpace($BaseSha) -or [string]::IsNullOrWhiteSpace($HeadSha)) {
        return @()
    }

    $uri = "https://api.github.com/repos/$GITHUB_OWNER/$GITHUB_REPO/compare/$BaseSha...$HeadSha"
    $headers = Get-GitHubHeaders
    $response = Invoke-RestMethod -Uri $uri -Headers $headers -Method Get -ErrorAction Stop
    if (-not $response.files) {
        return @()
    }

    if ([string]::IsNullOrWhiteSpace($REPO_CONTENT_PREFIX)) {
        return @($response.files)
    }

    $prefix = $REPO_CONTENT_PREFIX
    if (-not $prefix.EndsWith('/')) {
        $prefix = "$prefix/"
    }

    return @($response.files | Where-Object { $_.filename -like "$prefix*" })
}

function Get-LocalPortableCommitSha {
    if (Test-Path $LAST_SHA_FILE) {
        $sha = (Get-Content -Path $LAST_SHA_FILE -ErrorAction SilentlyContinue | Select-Object -First 1)
        if ($null -ne $sha) {
            return $sha.ToString().Trim()
        }
    }
    return $null
}

function Save-LocalPortableCommitSha {
    param([string]$Sha)
    if (-not [string]::IsNullOrWhiteSpace($Sha)) {
        Set-Content -Path $LAST_SHA_FILE -Value $Sha -Encoding UTF8
    }
}

function Get-DownloadUrlForFile {
    param(
        [string]$RepoPath,
        [string]$Ref
    )
    $encodedPath = [Uri]::EscapeDataString($RepoPath).Replace('%2F', '/')
    $uri = "https://api.github.com/repos/$GITHUB_OWNER/$GITHUB_REPO/contents/$encodedPath?ref=$Ref"
    $headers = Get-GitHubHeaders
    $meta = Invoke-RestMethod -Uri $uri -Headers $headers -Method Get -ErrorAction Stop
    return $meta.download_url
}

function Get-RemoteTreeFiles {
    param([string]$Ref)
    $headers = Get-GitHubHeaders
    $commitUri = "https://api.github.com/repos/$GITHUB_OWNER/$GITHUB_REPO/commits/$Ref"
    $commitMeta = Invoke-RestMethod -Uri $commitUri -Headers $headers -Method Get -ErrorAction Stop
    $treeSha = $commitMeta.commit.tree.sha
    $treeUri = "https://api.github.com/repos/$GITHUB_OWNER/$GITHUB_REPO/git/trees/$treeSha?recursive=1"
    $tree = Invoke-RestMethod -Uri $treeUri -Headers $headers -Method Get -ErrorAction Stop
    return @($tree.tree | Where-Object { $_.type -eq 'blob' })
}

function Sync-AllFilesFromTree {
    param(
        [array]$TreeFiles,
        [string]$Ref
    )
    $headers = Get-GitHubHeaders
    $anyApplied = $false
    foreach ($item in $TreeFiles) {
        $relativePath = [string]$item.path
        if ([string]::IsNullOrWhiteSpace($relativePath)) { continue }
        if (Should-PreservePath -RelativePath $relativePath) { continue }
        $targetPath = Join-Path $PORTABLE_ROOT ($relativePath -replace '/', '\')
        $targetDir = Split-Path -Parent $targetPath
        if (-not (Test-Path $targetDir)) {
            New-Item -Path $targetDir -ItemType Directory -Force | Out-Null
        }
        $rawUrl = "https://raw.githubusercontent.com/$GITHUB_OWNER/$GITHUB_REPO/$Ref/$relativePath"
        try {
            Invoke-WebRequest -Uri $rawUrl -Headers $headers -OutFile $targetPath -UseBasicParsing -ErrorAction Stop
            Write-Log "Full sync: updated $relativePath"
            $anyApplied = $true
            # Update EXE blob SHA tracking so Ensure-PortableExeUpToDate won't re-download
            $normalizedRelPath = $relativePath -replace '\\', '/'
            if ($normalizedRelPath -eq $PORTABLE_EXE_RELATIVE_PATH -and -not [string]::IsNullOrWhiteSpace([string]$item.sha)) {
                Save-LocalPortableExeSha -Sha ([string]$item.sha)
            }
        } catch {
            Write-Log "Full sync: failed to download ${relativePath}: $($_.Exception.Message)"
        }
    }
    return $anyApplied
}

function Get-RemoteContentMeta {
    param(
        [string]$RepoPath,
        [string]$Ref
    )

    $encodedPath = [Uri]::EscapeDataString($RepoPath).Replace('%2F', '/')
    $uri = "https://api.github.com/repos/$GITHUB_OWNER/$GITHUB_REPO/contents/$encodedPath?ref=$Ref"
    $headers = Get-GitHubHeaders
    return Invoke-RestMethod -Uri $uri -Headers $headers -Method Get -ErrorAction Stop
}

function Get-PortableRepoPath {
    param([string]$RelativePath)

    if ([string]::IsNullOrWhiteSpace($REPO_CONTENT_PREFIX)) {
        return $RelativePath
    }

    $prefix = $REPO_CONTENT_PREFIX.TrimEnd('/')
    return "$prefix/$RelativePath"
}

function Get-LocalPortableExeSha {
    if (Test-Path $LAST_EXE_SHA_FILE) {
        $sha = (Get-Content -Path $LAST_EXE_SHA_FILE -ErrorAction SilentlyContinue | Select-Object -First 1)
        if ($null -ne $sha) {
            return $sha.ToString().Trim()
        }
    }
    return $null
}

function Save-LocalPortableExeSha {
    param([string]$Sha)
    if (-not [string]::IsNullOrWhiteSpace($Sha)) {
        Set-Content -Path $LAST_EXE_SHA_FILE -Value $Sha -Encoding UTF8
    }
}

function Ensure-PortableExeUpToDate {
    param([string]$Ref)

    $refToUse = if ([string]::IsNullOrWhiteSpace($Ref)) { $GITHUB_BRANCH } else { $Ref }
    $repoPath = Get-PortableRepoPath -RelativePath $PORTABLE_EXE_RELATIVE_PATH
    $meta = Get-RemoteContentMeta -RepoPath $repoPath -Ref $refToUse

    if (-not $meta -or [string]::IsNullOrWhiteSpace([string]$meta.sha)) {
        Write-Log "EXE check skipped: could not read remote EXE metadata"
        return $false
    }

    $remoteExeSha = [string]$meta.sha
    $localExeSha = Get-LocalPortableExeSha
    $exeMissing = -not (Test-Path $APP_EXE)

    if (-not $exeMissing -and -not [string]::IsNullOrWhiteSpace($localExeSha) -and $localExeSha -eq $remoteExeSha) {
        return $false
    }

    Stop-App

    $targetDir = Split-Path -Parent $APP_EXE
    if (-not (Test-Path $targetDir)) {
        New-Item -Path $targetDir -ItemType Directory -Force | Out-Null
    }

    $downloadUrl = [string]$meta.download_url
    if ([string]::IsNullOrWhiteSpace($downloadUrl)) {
        $downloadUrl = Get-DownloadUrlForFile -RepoPath $repoPath -Ref $refToUse
    }

    $headers = Get-GitHubHeaders
    Invoke-WebRequest -Uri $downloadUrl -Headers $headers -OutFile $APP_EXE -UseBasicParsing -ErrorAction Stop
    Save-LocalPortableExeSha -Sha $remoteExeSha
    Write-Log "Updated executable: $PORTABLE_EXE_RELATIVE_PATH"
    return $true
}

function Should-PreservePath {
    param([string]$RelativePath)

    $normalized = ($RelativePath -replace '/', '\\').ToLowerInvariant()

    return ($normalized -like '.update_state\\*')
}

function Sync-ChangedPortableFilesFromGitHub {
    param(
        [array]$ChangedFiles,
        [string]$HeadSha
    )

    if (-not $ChangedFiles -or $ChangedFiles.Count -eq 0) {
        return $false
    }

    $headers = Get-GitHubHeaders
    $anyApplied = $false

    foreach ($file in $ChangedFiles) {
        $repoPath = [string]$file.filename
        if ([string]::IsNullOrWhiteSpace($repoPath)) {
            continue
        }

        $relativePath = $repoPath
        if (-not [string]::IsNullOrWhiteSpace($REPO_CONTENT_PREFIX)) {
            $prefix = $REPO_CONTENT_PREFIX
            if (-not $prefix.EndsWith('/')) {
                $prefix = "$prefix/"
            }

            if (-not $repoPath.StartsWith($prefix)) {
                continue
            }

            $relativePath = $repoPath.Substring($prefix.Length)
        }

        $relativePath = $relativePath.TrimStart('/')
        if ([string]::IsNullOrWhiteSpace($relativePath)) {
            continue
        }

        if (Should-PreservePath -RelativePath $relativePath) {
            Write-Log "Skipping preserved path: $repoPath"
            continue
        }

        $targetPath = Join-Path $PORTABLE_ROOT ($relativePath -replace '/', '\\')
        $status = [string]$file.status

        if ($status -eq 'removed') {
            if (Test-Path $targetPath) {
                Remove-Item -Path $targetPath -Force -ErrorAction SilentlyContinue
                Write-Log "Removed file: $relativePath"
                $anyApplied = $true
            }
            continue
        }

        if ($status -eq 'renamed' -and $file.previous_filename) {
            $oldRepoPath = [string]$file.previous_filename
            if (-not [string]::IsNullOrWhiteSpace($oldRepoPath)) {
                $oldRelative = $oldRepoPath

                if (-not [string]::IsNullOrWhiteSpace($REPO_CONTENT_PREFIX)) {
                    $prefix = $REPO_CONTENT_PREFIX
                    if (-not $prefix.EndsWith('/')) {
                        $prefix = "$prefix/"
                    }

                    if (-not $oldRepoPath.StartsWith($prefix)) {
                        $oldRelative = $null
                    } else {
                        $oldRelative = $oldRepoPath.Substring($prefix.Length)
                    }
                }

                if (-not [string]::IsNullOrWhiteSpace($oldRelative)) {
                    $oldRelative = $oldRelative.TrimStart('/')
                    if (-not (Should-PreservePath -RelativePath $oldRelative)) {
                        $oldTarget = Join-Path $PORTABLE_ROOT ($oldRelative -replace '/', '\\')
                        if (Test-Path $oldTarget) {
                            Remove-Item -Path $oldTarget -Force -ErrorAction SilentlyContinue
                            Write-Log "Removed renamed old file: $oldRelative"
                            $anyApplied = $true
                        }
                    }
                }
            }
        }

        $targetDir = Split-Path -Parent $targetPath
        if (-not (Test-Path $targetDir)) {
            New-Item -Path $targetDir -ItemType Directory -Force | Out-Null
        }

        $downloadUrl = if ($file.raw_url) { [string]$file.raw_url } else { Get-DownloadUrlForFile -RepoPath $repoPath -Ref $HeadSha }
        Invoke-WebRequest -Uri $downloadUrl -Headers $headers -OutFile $targetPath -UseBasicParsing -ErrorAction Stop
        Write-Log "Updated file: $relativePath"
        $anyApplied = $true
    }

    return $anyApplied
}

function Check-And-ApplyUpdates {
    try {
        $remoteSha = Get-RemotePortableCommitSha
        if ([string]::IsNullOrWhiteSpace($remoteSha)) {
            Write-Log "Update check skipped: could not read remote portable SHA"
            return $false
        }

        $localSha = Get-LocalPortableCommitSha
        if ([string]::IsNullOrWhiteSpace($localSha)) {
            Save-LocalPortableCommitSha -Sha $remoteSha
            Write-Log "Initialized update state to current remote SHA"
            return $false
        }

        if ($localSha -eq $remoteSha) {
            Write-Log "No portable updates"
            return $false
        }

        try {
            $changedFiles = Get-ChangedPortableFiles -BaseSha $localSha -HeadSha $remoteSha
        } catch {
            if (Is-NetworkUnavailableError -Exception $_.Exception) {
                return $false
            }

            # Compare failed — histories likely diverged due to a force-push from a clean repo.
            # Fall back to a full tree sync so all files (including config and EXE) are updated.
            Write-Log "Compare failed for local SHA '$localSha' (history may have diverged). Performing full sync to $remoteSha"
            try {
                $treeFiles = Get-RemoteTreeFiles -Ref $remoteSha
                Stop-App
                $fullSynced = Sync-AllFilesFromTree -TreeFiles $treeFiles -Ref $remoteSha
                Save-LocalPortableCommitSha -Sha $remoteSha
                if ($fullSynced) {
                    Write-Log "Full sync completed successfully"
                    return $true
                }
                Write-Log "Full sync: no files were applied"
            } catch {
                Write-Log "Full sync failed: $($_.Exception.Message)"
                Save-LocalPortableCommitSha -Sha $remoteSha
            }
            return $false
        }
        if (-not $changedFiles -or $changedFiles.Count -eq 0) {
            Save-LocalPortableCommitSha -Sha $remoteSha
            Write-Log "Portable SHA changed but no file-level portable changes to apply"
            return $false
        }

        Write-Log "Portable update detected: $($localSha) -> $($remoteSha), files: $($changedFiles.Count)"
        Stop-App

        $updated = Sync-ChangedPortableFilesFromGitHub -ChangedFiles $changedFiles -HeadSha $remoteSha
        Save-LocalPortableCommitSha -Sha $remoteSha

        if ($updated) {
            Write-Log "Portable changed files applied successfully"
            return $true
        }

        Write-Log "No applicable file changes were applied (all skipped/preserved)"
        return $false
    } catch {
        if (Is-NetworkUnavailableError -Exception $_.Exception) {
            return $false
        }

        Write-Log "Update check/apply failed: $($_.Exception.Message)"
        Write-Log "If repository is private, set GITHUB_TOKEN environment variable"
    }
    return $false
}

Ensure-Setup

if (Is-AnotherMonitorInstanceRunning) {
    Write-Log "Another monitor instance is already running; skipping this cycle"
    exit 0
}

$updatedNow = Check-And-ApplyUpdates
$appProcess = Get-AppProcess

if ($updatedNow -or -not $appProcess) {
    if ($updatedNow) {
        Write-Log "Restarting app after update..."
    } else {
        if (Was-AppStartedRecently -WindowSeconds 120) {
            Write-Log "$APP_NAME start suppressed: app was started recently"
            exit 0
        }
        Write-Log "$APP_NAME not running. Starting now..."
    }
    Start-App
    Start-Sleep -Milliseconds 900
    $appProcess = Get-AppProcess
    Ensure-AppFullscreen -AppProcess $appProcess
} else {
    Write-Log "$APP_NAME is running (PID: $($appProcess.Id))"
    Ensure-AppFullscreen -AppProcess $appProcess
}

# Keep last 500 lines of log
$logLines = @(Get-Content $LOG_FILE -ErrorAction SilentlyContinue)
if ($logLines.Count -gt 500) {
    $logLines[-500..-1] | Set-Content $LOG_FILE
}
