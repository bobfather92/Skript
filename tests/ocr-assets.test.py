from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OCR = ROOT / "vendor" / "ocr"

required_assets = {
    "tesseract.min.js": 50_000,
    "worker.min.js": 100_000,
    "lang/eng.traineddata.gz": 2_000_000,
    "core/tesseract-core.wasm.js": 3_000_000,
    "core/tesseract-core-lstm.wasm.js": 3_000_000,
    "core/tesseract-core-simd.wasm.js": 3_000_000,
    "core/tesseract-core-simd-lstm.wasm.js": 3_000_000,
    "core/tesseract-core-relaxedsimd.wasm.js": 3_000_000,
    "core/tesseract-core-relaxedsimd-lstm.wasm.js": 3_000_000,
}
for relative, minimum_size in required_assets.items():
    asset = OCR / relative
    assert asset.is_file(), f"Missing bundled OCR asset: {relative}"
    assert asset.stat().st_size >= minimum_size, f"Bundled OCR asset is incomplete: {relative}"

service = (ROOT / "skript.py").read_text(encoding="utf-8")
for relative in required_assets:
    assert f"'{relative}'" in service, f"OCR asset is not served: {relative}"

spec = (ROOT / "Skript.spec").read_text(encoding="utf-8")
assert "vendor/ocr" in spec

notices = (ROOT / "THIRD_PARTY_NOTICES.txt").read_text(encoding="utf-8")
assert "Tesseract.js" in notices
assert "tesseract english trained data" in notices.lower()

print("Bundled offline OCR asset and packaging tests passed.")
