import importlib.util
import io
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("skript_launcher", ROOT / "scriptforge.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

document_xml = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"><w:body>
  <w:p><w:pPr><w:pStyle w:val="Title"/></w:pPr><w:r><w:t>THE CLOCK HOUSE</w:t></w:r></w:p>
  <w:p><w:r><w:t>Written by</w:t></w:r></w:p>
  <w:p><w:r><w:t>Jamie Tester</w:t></w:r></w:p>
  <w:p><w:r><w:br w:type="page"/></w:r></w:p>
  <w:p><w:pPr><w:pStyle w:val="SceneHeading"/></w:pPr><w:r><w:t>INT. CLOCK HOUSE - NIGHT</w:t></w:r></w:p>
  <w:p><w:r><w:t>Rain strikes the windows.</w:t></w:r></w:p>
  <w:p><w:pPr><w:pStyle w:val="Character"/></w:pPr><w:r><w:t>MAYA</w:t></w:r></w:p>
  <w:p><w:pPr><w:pStyle w:val="Parenthetical"/></w:pPr><w:r><w:t>(quietly)</w:t></w:r></w:p>
  <w:p><w:pPr><w:pStyle w:val="Dialogue"/></w:pPr><w:r><w:t>It has started again.</w:t></w:r></w:p>
  <w:p><w:pPr><w:ind w:left="2880"/></w:pPr><w:r><w:t>ÉLODIE (V.O.)</w:t></w:r></w:p>
  <w:p><w:pPr><w:ind w:left="1440"/></w:pPr><w:r><w:t>I can hear it too.</w:t></w:r></w:p>
  <w:p><w:pPr><w:jc w:val="right"/></w:pPr><w:r><w:t>HARD CUT TO:</w:t></w:r></w:p>
</w:body></w:document>"""

styles_xml = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:styles xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">
  <w:style w:type="paragraph" w:styleId="Title"><w:name w:val="Title"/></w:style>
  <w:style w:type="paragraph" w:styleId="SceneHeading"><w:name w:val="Scene Heading"/></w:style>
  <w:style w:type="paragraph" w:styleId="Character"><w:name w:val="Character"/></w:style>
  <w:style w:type="paragraph" w:styleId="Parenthetical"><w:name w:val="Parenthetical"/></w:style>
  <w:style w:type="paragraph" w:styleId="Dialogue"><w:name w:val="Dialogue"/></w:style>
</w:styles>"""

core_xml = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<cp:coreProperties xmlns:cp="http://schemas.openxmlformats.org/package/2006/metadata/core-properties"
 xmlns:dc="http://purl.org/dc/elements/1.1/"><dc:title>The Clock House</dc:title></cp:coreProperties>"""

buffer = io.BytesIO()
with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as archive:
    archive.writestr("word/document.xml", document_xml)
    archive.writestr("word/styles.xml", styles_xml)
    archive.writestr("docProps/core.xml", core_xml)

result = module._import_word_bytes(buffer.getvalue(), ".docx", "Fallback Title")
assert result["coverData"] == {"title": "THE CLOCK HOUSE", "author": "Jamie Tester"}
assert result["titleHint"] == "THE CLOCK HOUSE"
assert [(line["type"], line["text"]) for line in result["lines"]] == [
    ("scene", "INT. CLOCK HOUSE - NIGHT"),
    ("action", "Rain strikes the windows."),
    ("character", "MAYA"),
    ("parenthetical", "(quietly)"),
    ("dialogue", "It has started again."),
    ("character", "ÉLODIE (V.O.)"),
    ("dialogue", "I can hear it too."),
    ("transition", "HARD CUT TO:"),
]
assert next(line for line in result["lines"] if line["text"] == "ÉLODIE (V.O.)")["_wordLeft"] == 2880
assert next(line for line in result["lines"] if line["text"] == "HARD CUT TO:")["_wordAlign"] == "right"

rtf = br"{\rtf1\ansi ACT I\par SCENE 1\par HAMLET: To be, or not to be.\par}"
legacy = module._import_word_bytes(rtf, ".doc", "Legacy Stage Play")
assert legacy["converter"] == "RTF reader"
assert any(line["type"] == "act" for line in legacy["lines"])
assert any(line["type"] == "character" and line["text"] == "HAMLET" for line in legacy["lines"])
assert any(line["type"] == "dialogue" and "To be" in line["text"] for line in legacy["lines"])

print("Word DOCX and legacy DOC/RTF import regression tests passed.")
