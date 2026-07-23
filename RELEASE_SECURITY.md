# Release signing and antivirus reputation

There is no application flag or source-code marker that can make antivirus products trust a program. Skript must establish a verifiable publisher identity and ship the exact same reviewed binary to every user.

## What has been changed in this repository

- UPX executable compression is disabled in every PyInstaller specification. Packed binaries save space but add no value to Skript and make static inspection harder.
- Clean release builds compile a project-specific PyInstaller 6.21.0 bootloader instead of reusing its widespread precompiled bootloader. PyInstaller documents this as a way to reduce false positives caused by the common bootloader fingerprint: https://pyinstaller.org/en/stable/bootloader-building.html
- The release workflow signs `Skript.exe` before it is placed inside the installer, then signs the completed setup executable.
- Both signatures use SHA-256 and an RFC 3161 timestamp and are verified before release artifacts are uploaded.
- Tagged GitHub releases fail if signing is not configured. Manually dispatched unsigned builds are clearly named `UNSIGNED-TEST-BUILD` and must not be distributed.
- SHA-256 checksums are generated only after signing, because signing changes the file hash.

Microsoft explains that Authenticode establishes authorship and integrity, and that timestamping keeps a signature verifiable after its certificate expires:

- https://learn.microsoft.com/windows/win32/seccrypto/time-stamping-authenticode-signatures
- https://learn.microsoft.com/windows/apps/package-and-deploy/smartscreen-reputation

Signing greatly improves trust and replaces **Unknown Publisher** with the verified publisher name. It does not guarantee that a brand-new file hash will never receive a reputation warning. Microsoft says each new binary hash must still build reputation; Microsoft Store distribution is the only route that avoids SmartScreen download warnings from the first download.

## Recommended: Microsoft Azure Artifact Signing

Microsoft currently recommends Azure Artifact Signing for Windows software distributed outside the Microsoft Store. Use a **Public Trust** certificate profile so Windows consumer devices trust it. Public Trust identity validation is available to organisations in the United Kingdom, but Microsoft's current eligibility page limits individual-developer validation to the USA and Canada. A UK developer publishing without a registered organisation should use a traditional trusted certificate or Microsoft Store distribution instead.

1. Create an Artifact Signing account, complete identity validation, and create a Public Trust certificate profile:
   https://learn.microsoft.com/azure/artifact-signing/quickstart
2. Create a Microsoft Entra application or managed identity with a federated GitHub credential.
3. Assign it the **Artifact Signing Certificate Profile Signer** role for the certificate profile.
4. Add these GitHub Actions secrets:
   - `AZURE_CLIENT_ID`
   - `AZURE_TENANT_ID`
   - `AZURE_SUBSCRIPTION_ID`
5. Add these GitHub Actions repository variables:
   - `AZURE_ARTIFACT_SIGNING_ENDPOINT` — for example, the regional `https://...codesigning.azure.net/` endpoint shown by Azure
   - `AZURE_ARTIFACT_SIGNING_ACCOUNT`
   - `AZURE_ARTIFACT_SIGNING_PROFILE`
   - `AZURE_ARTIFACT_SIGNING_EXPECTED_PUBLISHER` — a stable identifying part of the validated certificate subject, such as the registered organisation name
6. Run the Windows release workflow manually once. Confirm both uploaded executables report a valid signature before creating a release tag.

The workflow uses Microsoft's official Artifact Signing action and OIDC login, so no private signing key is stored in the repository:

- https://github.com/Azure/artifact-signing-action

Keep the same signing account and publisher identity for future releases. Publisher consistency is one of the signals used by reputation systems.

## Alternative: a traditional CA certificate

An RSA Authenticode code-signing certificate from a provider in the Microsoft Trusted Root Program can also be used. A self-signed certificate will not establish public trust. Microsoft no longer gives new EV-signed files an automatic SmartScreen reputation advantage over OV-signed files, so do not buy EV solely for that reason.

Install the certificate and private key through the CA's supported hardware or cloud provider, install the Windows SDK signing tools, build the app and installer, then run:

```powershell
./tools/Sign-Release.ps1 -CertificateThumbprint 'YOUR_CERTIFICATE_SHA1_THUMBPRINT'
```

The script signs and timestamps both release executables and fails if either signature cannot be verified. Never commit a PFX file, private key, certificate password, access token, or signing PIN.

## Norton false-positive process

Norton requires the actual detected file, the detection name, and the Alert ID from the detection window. A support email alone is not the documented submission route.

1. Build, sign, timestamp, and verify the final installer.
2. Generate `SHA256SUMS.txt`. Do not rebuild or modify the installer after this point.
3. Update Norton and reproduce the detection to record its exact detection name and Alert ID.
4. Place the single signed installer in an unencrypted ZIP or RAR archive. Norton accepts one file per archive, up to 500 MB, and says the archive must not be password protected.
5. Submit it as a **False positive** through https://submit.norton.com and retain the Request ID.
6. When Norton clears the file, distribute that exact installer with the same SHA-256 hash. A rebuild is a different file and may need a new review.

Norton's current instructions are here:

- https://support.norton.com/sp/en/ca/norton-antivirus/17.9.0.12/solutions/kb20090410134005EN

Do not ask normal users to disable antivirus protection. Temporary exclusions are suitable only for controlled developer testing after the binary and build machine have been independently checked.

## Release checklist

- Build on a clean, patched Windows runner from a tagged source revision.
- Keep PyInstaller, Python, and dependencies pinned and reviewed; retain the project-specific bootloader build.
- Sign the application before building the installer.
- Sign and timestamp the installer.
- Run `tools/Test-Authenticode.ps1` against both executables.
- Confirm the verified certificate subject contains the configured expected publisher; the release workflow rejects a valid signature from an unexpected identity.
- Pass the automated install, first-launch, reopen, Repair, Update and Uninstall lifecycle without changing the project-safety fixtures.
- Generate and publish the SHA-256 checksum after signing.
- Scan the final binary locally with fully updated security software.
- Submit the exact final hash to Norton when a false positive occurs.
- Publish from a stable HTTPS domain; consider Microsoft Store distribution for the strongest first-download reputation.
