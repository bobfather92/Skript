import ast
import base64
import gzip
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
VERSION = (ROOT / "VERSION.txt").read_text(encoding="utf-8").strip()
assert re.fullmatch(r"\d+\.\d+\.\d+\.\d+", VERSION)
assert sorted(path.name for path in ROOT.glob("RELEASE_NOTES_*.md")) == [
    f"RELEASE_NOTES_{VERSION}.md"
]

html = (ROOT / "Skript.html").read_text(encoding="utf-8")
python_source = (ROOT / "skript.py").read_text(encoding="utf-8")
python_tree = ast.parse(python_source)
embedded_assignment = next(
    node for node in python_tree.body
    if isinstance(node, ast.Assign)
    and any(isinstance(target, ast.Name) and target.id == "_HTML_B64" for target in node.targets)
)
embedded_html = gzip.decompress(base64.b64decode(ast.literal_eval(embedded_assignment.value))).decode("utf-8")
assert embedded_html == html, "Packaged HTML must match Skript.html"

assert f"Version {VERSION}" in html
assert f"showChangesVersion('{VERSION}')" in html
assert f"APP_VERSION = '{VERSION}'" in (ROOT / "installer" / "skript_installer.py").read_text(encoding="utf-8")
assert f"VERSION = '{VERSION}'" in (ROOT / "Install.py").read_text(encoding="utf-8")
assert f"name='Skript-Setup-{VERSION}'" in (ROOT / "SkriptInstaller.spec").read_text(encoding="utf-8")
assert f"Skript-Setup-{VERSION}.exe" in (ROOT / "installer" / "README.txt").read_text(encoding="utf-8")


for name in ("Skript.spec", "SkriptInstaller.spec", "SkriptDiagnostic.spec"):
    source = (ROOT / name).read_text(encoding="utf-8")
    assert "upx=True" not in source, f"{name} must not enable UPX"
    assert "upx=False" in source, f"{name} must explicitly disable UPX"

legacy_installer = (ROOT / "Install.py").read_text(encoding="utf-8")
assert "'--noupx'" in legacy_installer

workflow = (ROOT / ".github/workflows/windows-release.yml").read_text(encoding="utf-8")
for required in (
    "azure/artifact-signing-action@v2",
    "timestamp-rfc3161: http://timestamp.acs.microsoft.com",
    "Tagged releases must be Authenticode-signed",
    "Test-Authenticode.ps1",
    "--noupx",
    "PYINSTALLER_COMPILE_BOOTLOADER",
    "PyInstaller==6.21.0",
    "SHA256SUMS.txt",
    "AZURE_ARTIFACT_SIGNING_EXPECTED_PUBLISHER",
    "release-lifecycle.ps1",
    "playwright test",
    "tools/embed_html.py --check",
    "Release tag must be $expectedTag",
    "gh release create",
    "--draft",
    "--verify-tag",
    "portable.zip",
):
    assert required in workflow, f"Missing release safeguard: {required}"

assert f"RELEASE_NOTES_{VERSION}.md" in {
    path.name for path in ROOT.glob("RELEASE_NOTES_*.md")
}

security_guide = (ROOT / "RELEASE_SECURITY.md").read_text(encoding="utf-8")
assert "https://submit.norton.com" in security_guide
assert "Unknown Publisher" in security_guide
assert "Do not ask normal users to disable antivirus protection" in security_guide

signature_check = (ROOT / "tools" / "Test-Authenticode.ps1").read_text(encoding="utf-8")
assert "ExpectedPublisher" in signature_check
assert "1.3.6.1.5.5.7.3.3" in signature_check

local_signing = (ROOT / "tools" / "Sign-Release.ps1").read_text(encoding="utf-8")
assert "-ExpectedPublisher $certificate.Subject" in local_signing

print("Release signing and antivirus reputation safeguards passed.")
