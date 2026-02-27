# Prayer Time Display App Monitor + GitHub Portable Updater
# Checks every minute for changes under portable/ and downloads only changed files.

$APP_NAME = "PrayerTimeDisplay"
$APP_EXE = "C:\portable\standalone\PrayerTimeDisplay.exe"
$LOG_FILE = "C:\portable\startupscripts\app_monitor.log"

$GITHUB_OWNER = "Ehai-development"
$GITHUB_REPO = "prayertimes-portable"
$GITHUB_BRANCH = "main"
$GITHUB_TOKEN_FILE = Join-Path (Split-Path -Parent $PSCommandPath) "github_token.txt"
$REPO_CONTENT_PREFIX = ""
$USE_GITHUB_TOKEN = $false

$PORTABLE_ROOT = Split-Path -Parent (Split-Path -Parent $APP_EXE)
$STATE_DIR = Join-Path $PORTABLE_ROOT ".update_state"
$LAST_SHA_FILE = Join-Path $STATE_DIR "portable_last_sha.txt"

function Write-Log {
    param([string]$Message)
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "$timestamp - $Message"
    Add-Content -Path $LOG_FILE -Value $logMessage
    Write-Host $logMessage
}

function Ensure-Setup {
    if (-not (Test-Path $LOG_FILE)) {
        New-Item -Path $LOG_FILE -ItemType File -Force | Out-Null
    }
    if (-not (Test-Path $STATE_DIR)) {
        New-Item -Path $STATE_DIR -ItemType Directory -Force | Out-Null
    }
}

function Get-GitHubHeaders {
    $headers = @{
        "User-Agent" = "PrayerTimeMonitor"
        "Accept" = "application/vnd.github+json"
    }
    if ($USE_GITHUB_TOKEN) {
        $token = $env:GITHUB_TOKEN
        if ([string]::IsNullOrWhiteSpace($token) -and (Test-Path $GITHUB_TOKEN_FILE)) {
            try {
                $token = (Get-Content -Path $GITHUB_TOKEN_FILE -ErrorAction SilentlyContinue | Select-Object -First 1)
            } catch {
                $token = $null
            }
        }

        if (-not [string]::IsNullOrWhiteSpace($token)) {
            $headers["Authorization"] = "token $($token.Trim())"
        }
    }
    return $headers
}

function Get-AppProcess {
    return Get-Process -Name $APP_NAME -ErrorAction SilentlyContinue
}

function Stop-App {
    $p = Get-AppProcess
    if ($p) {
        try {
            $p | Stop-Process -Force -ErrorAction Stop
            Write-Log "Stopped $APP_NAME for update"
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

    try {
        $workingDir = Split-Path -Parent $APP_EXE
        $workingDir = Split-Path -Parent $workingDir
        $proc = Start-Process -FilePath $APP_EXE -WorkingDirectory $workingDir -PassThru -ErrorAction Stop
        Write-Log "Started $APP_NAME (PID: $($proc.Id))"
    } catch {
        Write-Log "Failed to start ${APP_NAME}: $($_.Exception.Message)"
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

function Should-PreservePath {
    param([string]$RelativePath)

    $normalized = ($RelativePath -replace '/', '\\').ToLowerInvariant()

    if ($normalized -eq 'config\\announcements.txt' -or $normalized -eq 'config\\ramadhanannouncements.txt') {
        return $false
    }

    return ($normalized -like 'config\\*' -or $normalized -like 'data\\*' -or $normalized -like '.update_state\\*')
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
            Write-Log "Compare failed for local SHA '$localSha'. Resetting state to remote SHA."
            Save-LocalPortableCommitSha -Sha $remoteSha
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
        Write-Log "Update check/apply failed: $($_.Exception.Message)"
        Write-Log "If repository is private, set GITHUB_TOKEN env var or create token file: $GITHUB_TOKEN_FILE"
    }
    return $false
}

Ensure-Setup

$updatedNow = Check-And-ApplyUpdates
$appProcess = Get-AppProcess

if ($updatedNow -or -not $appProcess) {
    if ($updatedNow) {
        Write-Log "Restarting app after update..."
    } else {
        Write-Log "$APP_NAME not running. Starting now..."
    }
    Start-App
} else {
    Write-Log "$APP_NAME is running (PID: $($appProcess.Id))"
}

# Keep last 500 lines of log
$logLines = @(Get-Content $LOG_FILE -ErrorAction SilentlyContinue)
if ($logLines.Count -gt 500) {
    $logLines[-500..-1] | Set-Content $LOG_FILE
}
