[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [ValidateScript({ Test-Path -LiteralPath $_ -PathType Leaf })]
    [string] $SetupPath,

    [int] $TimeoutSeconds = 90
)

$ErrorActionPreference = 'Stop'
$setup = (Resolve-Path -LiteralPath $SetupPath).Path
$version = (Get-Content -LiteralPath (Join-Path $PSScriptRoot '..\VERSION.txt') -Raw).Trim()
$testRoot = Join-Path (Join-Path $PSScriptRoot '..\tmp') "release-lifecycle-$([guid]::NewGuid().ToString('N'))"
$install = Join-Path $testRoot 'LocalAppData\Programs\Skript'
$runtime = Join-Path $install '_runtime_1_0_0_4'
$projects = Join-Path $testRoot 'Documents\Skript\scripts'
$legacyProjects = Join-Path $testRoot ('Documents\Script' + 'Forge\scripts')
$projectRoots = @($projects, $legacyProjects)
$registryPath = 'HKCU:\Software\SkriptReleaseTests\Skript'
$startLink = Join-Path $testRoot 'AppData\Microsoft\Windows\Start Menu\Programs\Skript\Skript.lnk'
$originalMode = $env:SKRIPT_INSTALLER_TEST_MODE
$originalRoot = $env:SKRIPT_INSTALLER_TEST_ROOT

function Invoke-CheckedProcess {
    param([string] $FilePath, [string[]] $Arguments, [string] $Label, [string] $WorkingDirectory = '')
    $encodedArguments = $Arguments | ForEach-Object {
        if ($_ -match '[\s"]') { '"' + $_.Replace('"', '\"') + '"' } else { $_ }
    }
    if ($WorkingDirectory) {
        $process = Start-Process -FilePath $FilePath -ArgumentList $encodedArguments -PassThru -WindowStyle Hidden -WorkingDirectory $WorkingDirectory
    } else {
        $process = Start-Process -FilePath $FilePath -ArgumentList $encodedArguments -PassThru -WindowStyle Hidden
    }
    if (-not $process.WaitForExit($TimeoutSeconds * 1000)) {
        Stop-Process -Id $process.Id -Force -ErrorAction SilentlyContinue
        throw "$Label timed out after $TimeoutSeconds seconds."
    }
    if ($process.ExitCode -ne 0) {
        throw "$Label failed with exit code $($process.ExitCode)."
    }
}

function Get-ProjectHashes {
    $result = @{}
    foreach ($root in $projectRoots) {
        if (-not (Test-Path -LiteralPath $root)) { continue }
        $label = Split-Path -Leaf (Split-Path -Parent $root)
        Get-ChildItem -LiteralPath $root -File -Recurse | ForEach-Object {
            $relative = $_.FullName.Substring($root.Length).TrimStart('\')
            $result["$label\$relative"] = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash
        }
    }
    return $result
}

function Assert-ProjectsUnchanged {
    param([hashtable] $Expected, [string] $Stage)
    $actual = Get-ProjectHashes
    if ($actual.Count -ne $Expected.Count) { throw "$Stage changed the number of user project files." }
    foreach ($name in $Expected.Keys) {
        if ($actual[$name] -ne $Expected[$name]) { throw "$Stage changed user project '$name'." }
    }
}

function Invoke-AppSelfTest {
    param([string] $Stage)
    $app = Join-Path $install 'Skript.exe'
    $report = Join-Path $testRoot "self-test-$Stage.json"
    $env:SKRIPT_SELF_TEST_REPORT = $report
    try {
        Invoke-CheckedProcess -FilePath $app -Arguments @('--release-self-test') -Label "$Stage application launch"
    } finally {
        Remove-Item Env:\SKRIPT_SELF_TEST_REPORT -ErrorAction SilentlyContinue
    }
    $result = Get-Content -LiteralPath $report -Raw | ConvertFrom-Json
    if (-not $result.ok -or $result.version -ne $version) {
        throw "$Stage application self-test did not validate the packaged release."
    }
    foreach ($required in @('version','resources','tkinter','embedded-html','loopback-service')) {
        if ($required -notin $result.checks) { throw "$Stage application self-test missed '$required'." }
    }
}

try {
    New-Item -ItemType Directory -Path $projects -Force | Out-Null
    New-Item -ItemType Directory -Path $legacyProjects -Force | Out-Null
    Set-Content -LiteralPath (Join-Path $projects 'Feature Film.skript') -Value '{"title":"Keep me"}' -Encoding utf8
    Set-Content -LiteralPath (Join-Path $projects 'Television Project.script') -Value 'user project data' -Encoding utf8
    New-Item -ItemType Directory -Path (Join-Path $projects 'Backups') -Force | Out-Null
    Set-Content -LiteralPath (Join-Path $projects 'Backups\recovery.recover') -Value 'recovery data' -Encoding utf8
    Set-Content -LiteralPath (Join-Path $legacyProjects 'Legacy Project.script') -Value 'legacy user project data' -Encoding utf8
    $projectHashes = Get-ProjectHashes

    $env:SKRIPT_INSTALLER_TEST_MODE = '1'
    $env:SKRIPT_INSTALLER_TEST_ROOT = $testRoot

    Invoke-CheckedProcess -FilePath $setup -Arguments @('--silent','--no-desktop') -Label 'Clean install'
    if (-not (Test-Path -LiteralPath (Join-Path $install 'Skript.exe'))) { throw 'Clean install did not create Skript.exe.' }
    if (-not (Test-Path -LiteralPath $runtime -PathType Container)) { throw 'Clean install did not create the versioned application runtime.' }
    if ((Get-Content -LiteralPath (Join-Path $install 'version.txt') -Raw).Trim() -ne $version) { throw 'Clean install wrote the wrong version.' }
    if (-not (Test-Path -LiteralPath $startLink)) { throw 'Clean install did not create its Start Menu shortcut.' }
    Assert-ProjectsUnchanged $projectHashes 'Clean install'
    Invoke-AppSelfTest 'first-launch'
    Invoke-AppSelfTest 'reopen'

    Set-Content -LiteralPath (Join-Path $install 'obsolete-old-version.dll') -Value 'remove me' -Encoding ascii
    $interruptedStaging = "$install.installing"
    New-Item -ItemType Directory -Path $interruptedStaging -Force | Out-Null
    Set-Content -LiteralPath (Join-Path $interruptedStaging 'partial-install.tmp') -Value 'interrupted setup' -Encoding ascii
    Invoke-CheckedProcess -FilePath $setup -Arguments @('--silent','--no-desktop','--repair') -Label 'Same-version repair' -WorkingDirectory $install
    if (Test-Path -LiteralPath (Join-Path $install 'obsolete-old-version.dll')) { throw 'Repair retained an obsolete application file.' }
    if (Test-Path -LiteralPath $interruptedStaging) { throw 'Repair retained an incomplete staging folder.' }
    if (-not (Test-Path -LiteralPath $runtime -PathType Container)) { throw 'Repair did not retain the versioned application runtime.' }
    Assert-ProjectsUnchanged $projectHashes 'Repair'
    Invoke-AppSelfTest 'repair'

    Set-Content -LiteralPath (Join-Path $install 'version.txt') -Value '0.9.9.9' -Encoding ascii
    Set-ItemProperty -LiteralPath $registryPath -Name DisplayVersion -Value '0.9.9.9'
    Set-Content -LiteralPath (Join-Path $install 'obsolete-update-file.dll') -Value 'remove me' -Encoding ascii
    Invoke-CheckedProcess -FilePath $setup -Arguments @('--silent','--no-desktop') -Label 'Version update'
    if ((Get-Content -LiteralPath (Join-Path $install 'version.txt') -Raw).Trim() -ne $version) { throw 'Update did not restore the current version.' }
    if (Test-Path -LiteralPath (Join-Path $install 'obsolete-update-file.dll')) { throw 'Update retained an obsolete application file.' }
    if (-not (Test-Path -LiteralPath $runtime -PathType Container)) { throw 'Update did not retain the versioned application runtime.' }
    Assert-ProjectsUnchanged $projectHashes 'Update'
    Invoke-AppSelfTest 'update'

    Invoke-CheckedProcess -FilePath $setup -Arguments @('--uninstall-worker', $install, '--silent') -Label 'Uninstall'
    if (Test-Path -LiteralPath $install) { throw 'Uninstall left application files behind.' }
    if (Test-Path -LiteralPath $startLink) { throw 'Uninstall left the Start Menu shortcut behind.' }
    if (Test-Path -LiteralPath $registryPath) { throw 'Uninstall left its registration behind.' }
    Assert-ProjectsUnchanged $projectHashes 'Uninstall'

    Write-Host "Release lifecycle passed: install, first launch, reopen, repair, update and uninstall ($version)."
    Write-Host "Verified $($projectHashes.Count) project, backup and recovery files remained unchanged."
} finally {
    if ($null -eq $originalMode) { Remove-Item Env:\SKRIPT_INSTALLER_TEST_MODE -ErrorAction SilentlyContinue }
    else { $env:SKRIPT_INSTALLER_TEST_MODE = $originalMode }
    if ($null -eq $originalRoot) { Remove-Item Env:\SKRIPT_INSTALLER_TEST_ROOT -ErrorAction SilentlyContinue }
    else { $env:SKRIPT_INSTALLER_TEST_ROOT = $originalRoot }
    Remove-Item -LiteralPath $registryPath -Recurse -Force -ErrorAction SilentlyContinue
    if (Test-Path -LiteralPath $testRoot) {
        $resolvedRoot = (Resolve-Path -LiteralPath $testRoot).Path
        $tmpRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\tmp')).Path
        if (-not $resolvedRoot.StartsWith($tmpRoot, [System.StringComparison]::OrdinalIgnoreCase)) {
            throw 'Refusing to clean a release-test directory outside the workspace tmp folder.'
        }
        Remove-Item -LiteralPath $resolvedRoot -Recurse -Force
    }
}
