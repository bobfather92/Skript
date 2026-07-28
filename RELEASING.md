# Releasing Skript

This checklist prepares a signed, reviewed GitHub release without exposing signing credentials or publishing unverified files.

## 1. Freeze and verify the source

1. Confirm `VERSION.txt` contains the intended four-part Windows build number.
2. Update the matching release notes and in-app Changes panel.
3. Run `python tools/embed_html.py --check`.
4. Run every JavaScript and Python source regression test.
5. Run `pnpm e2e` and require zero failures.
6. Confirm the working tree contains only intended release changes.

Never commit generated installers, portable packages, signing certificates, local scripts, recovery data or collaboration secrets.

## 2. Commit and tag

The release tag must exactly match `v` followed by `VERSION.txt`. For build `1.1.0.0`, use:

```powershell
git tag -a v1.1.0.0 -m "Skript 1.1 official release"
git push origin main
git push origin v1.1.0.0
```

The workflow rejects a mismatched tag and refuses to create an unsigned tagged build.

## 3. Review the draft release

After the Windows release workflow succeeds:

1. Open the draft GitHub Release created by the workflow.
2. Confirm it contains the signed setup executable, portable ZIP and `SHA256SUMS.txt`.
3. Download the files from GitHub and verify their SHA-256 checksums.
4. Verify both executable signatures, publisher identity and RFC 3161 timestamps.
5. Test clean install, first launch, reopen, same-version repair, update from an older build and uninstall on Windows.
6. Confirm representative projects, backups and recovery copies remain unchanged.
7. Review the release notes and only then publish the draft.

Do not replace artifacts attached to an already published release. If a published build needs correction, increment the version and issue a new release.

Signing configuration and antivirus reputation guidance are documented in [RELEASE_SECURITY.md](RELEASE_SECURITY.md).
