[CmdletBinding()]
param(
    [Parameter(Mandatory = $true, ValueFromPipeline = $true)]
    [ValidateNotNullOrEmpty()]
    [string[]] $Path,

    [string] $ExpectedPublisher = ''
)

$ErrorActionPreference = 'Stop'
$failed = $false

foreach ($item in $Path) {
    $resolved = Resolve-Path -LiteralPath $item
    $signature = Get-AuthenticodeSignature -LiteralPath $resolved.Path
    if ($signature.Status -ne [System.Management.Automation.SignatureStatus]::Valid) {
        Write-Error "Invalid Authenticode signature on '$($resolved.Path)': $($signature.Status) $($signature.StatusMessage)"
        $failed = $true
        continue
    }

    if (-not $signature.SignerCertificate -or -not $signature.TimeStamperCertificate) {
        Write-Error "'$($resolved.Path)' must have both a publisher signature and an RFC 3161 timestamp."
        $failed = $true
        continue
    }

    $codeSigningOid = '1.3.6.1.5.5.7.3.3'
    if (-not ($signature.SignerCertificate.EnhancedKeyUsageList.ObjectId.Value -contains $codeSigningOid)) {
        Write-Error "'$($resolved.Path)' was not signed with a code-signing certificate."
        $failed = $true
        continue
    }

    if ($ExpectedPublisher -and
        $signature.SignerCertificate.Subject.IndexOf($ExpectedPublisher, [System.StringComparison]::OrdinalIgnoreCase) -lt 0) {
        Write-Error "Unexpected publisher on '$($resolved.Path)'. Expected '$ExpectedPublisher'; received '$($signature.SignerCertificate.Subject)'."
        $failed = $true
        continue
    }

    Write-Host "Valid signature: $($resolved.Path)"
    Write-Host "  Publisher: $($signature.SignerCertificate.Subject)"
    Write-Host "  Timestamp: $($signature.TimeStamperCertificate.Subject)"
    Write-Host "  Thumbprint: $($signature.SignerCertificate.Thumbprint)"
}

if ($failed) {
    exit 1
}
