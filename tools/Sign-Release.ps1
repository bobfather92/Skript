[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [ValidatePattern('^[A-Fa-f0-9 ]{40}$')]
    [string] $CertificateThumbprint,

    [string[]] $Path = @(
        'build_artifacts/app/Skript/Skript.exe',
        "build_artifacts/installer/Skript-Setup-$((Get-Content -LiteralPath 'VERSION.txt' -Raw).Trim()).exe"
    ),

    [string] $TimestampUrl = 'http://timestamp.acs.microsoft.com',

    [switch] $MachineStore
)

$ErrorActionPreference = 'Stop'
$thumbprint = $CertificateThumbprint.Replace(' ', '').ToUpperInvariant()
$storeLocation = if ($MachineStore) { 'LocalMachine' } else { 'CurrentUser' }
$certificatePath = "Cert:\$storeLocation\My\$thumbprint"
$certificate = Get-Item -LiteralPath $certificatePath -ErrorAction SilentlyContinue

if (-not $certificate) {
    throw "Code-signing certificate $thumbprint was not found in $storeLocation\My."
}
if (-not $certificate.HasPrivateKey) {
    throw 'The selected certificate does not have an accessible private key.'
}
if ($certificate.NotAfter -le (Get-Date)) {
    throw "The selected certificate expired on $($certificate.NotAfter)."
}
$codeSigningOid = '1.3.6.1.5.5.7.3.3'
if (-not ($certificate.EnhancedKeyUsageList.ObjectId.Value -contains $codeSigningOid)) {
    throw 'The selected certificate is not valid for code signing.'
}

$signTool = Get-Command 'signtool.exe' -ErrorAction SilentlyContinue
$signToolPath = if ($signTool) { $signTool.Source } else { $null }
if (-not $signTool) {
    $kitsRoot = Join-Path ${env:ProgramFiles(x86)} 'Windows Kits\10\bin'
    $candidate = Get-ChildItem -LiteralPath $kitsRoot -Filter 'signtool.exe' -Recurse -ErrorAction SilentlyContinue |
        Where-Object FullName -Match '\\x64\\signtool\.exe$' |
        Sort-Object FullName -Descending |
        Select-Object -First 1
    if ($candidate) { $signToolPath = $candidate.FullName }
}
if (-not $signToolPath) {
    throw 'SignTool.exe was not found. Install the Windows SDK signing tools first.'
}

$resolvedFiles = foreach ($item in $Path) {
    (Resolve-Path -LiteralPath $item).Path
}

foreach ($file in $resolvedFiles) {
    $arguments = @(
        'sign', '/v', '/fd', 'SHA256', '/sha1', $thumbprint,
        '/s', 'My', '/tr', $TimestampUrl, '/td', 'SHA256',
        '/d', 'Skript Professional Screenwriting'
    )
    if ($MachineStore) { $arguments += '/sm' }
    $arguments += $file

    & $signToolPath @arguments
    if ($LASTEXITCODE -ne 0) {
        throw "SignTool failed for '$file' with exit code $LASTEXITCODE."
    }
}

& (Join-Path $PSScriptRoot 'Test-Authenticode.ps1') -Path $resolvedFiles -ExpectedPublisher $certificate.Subject
