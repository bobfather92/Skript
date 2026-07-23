import importlib.util
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("skript_launcher", ROOT / "skript.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

html = module._build_pdf_html(
    "Layout Test",
    {},
    [
        {"type": "scene", "text": "INT. NEWSROOM - DAY"},
        {"type": "action", "text": "Phones ring across the crowded room."},
        {"type": "character", "text": "MAYA"},
        {"type": "dialogue", "text": "We go live in thirty seconds."},
        {"type": "parenthetical", "text": "(quietly)"},
        {"type": "transition", "text": "CUT TO:"},
    ],
    "film",
    False,
    True,
)

expected_css = [
    "margin: 1in 0.75in 1in 1.5in",
    ".el-scene + .el-action { margin-top: 12pt; }",
    ".speech + .el-action { margin-top: 12pt; }",
    "margin-left: 2.0in",
    "margin-left: 1.0in",
    "margin-right: 1.25in",
    "margin-left: 1.5in",
    "margin-right: 2.0in",
]
for declaration in expected_css:
    assert declaration in html, declaration

assert html.index("el-scene") < html.index("el-action")
assert html.index("el-character") < html.index("el-dialogue")
assert 'class="el-transition">CUT TO:</div>' in html
transition_css = html.split('.el-transition {', 1)[1].split('}', 1)[0]
assert 'text-align: left' in transition_css

fallback_source = (ROOT / 'skript.py').read_text(encoding='utf-8')
assert "draw(text.upper(), left_default, True, cols=58)" in fallback_source

explicit = module._build_pdf_html(
    "Parity Test",
    {},
    [],
    "film",
    False,
    True,
    [
        {"type": "scene", "text": "INT. FIRST ROOM - DAY"},
        {"type": "_break", "text": ""},
        {"type": "_page-num", "text": "2."},
        {"type": "scene", "text": "INT. SECOND ROOM - NIGHT", "pageLeading": True},
        {"type": "character", "text": "MAYA"},
        {"type": "dialogue", "text": "This layout came from the editor."},
        {
            "type": "dual-dialogue",
            "columns": [
                [{"type": "character", "text": "MAYA"}, {"type": "dialogue", "text": "Left."}],
                [{"type": "character", "text": "JO"}, {"type": "dialogue", "text": "Right."}],
            ],
        },
    ],
)
assert "script-body explicit-layout" in explicit
assert explicit.count('class="pg-break"') == 1
assert explicit.count('class="page-num-stamp"') == 1
assert 'el-scene page-leading' in explicit
assert explicit.count('class="dual-col"') == 2
assert explicit.index("INT. FIRST ROOM - DAY") < explicit.index("INT. SECOND ROOM - NIGHT")

play = module._build_pdf_html(
    "Stage Test",
    {
        "title": "A Stage Test", "author": "Test Writer",
        "contact1": "Private and Confidential", "contact2": "Test Productions",
        "contact3": "writer@example.test", "contact4": "+44 0000 000000",
        "rights1": "All rights reserved", "rights2": "Copyright 2026",
    },
    [
        {"type": "act", "text": "ACT I"},
        {"type": "scene", "text": "SCENE 1"},
        {"type": "stage-direction", "text": "The lights fade slowly."},
        {"type": "character", "text": "MAYA"},
        {"type": "dialogue", "text": "We begin."},
    ],
    "play", True, True,
)
assert '<body class="format-play">' in play
assert 'height: 238mm' in play
assert 'position: absolute' in play
assert '.format-play .el-character' in play
assert '.format-play .el-dialogue' in play
assert '(The lights fade slowly.)' in play
assert 'grid-template-columns: minmax(0, 1fr) minmax(0, 1fr)' in play
assert 'writer@example.test' in play and '+44 0000 000000' in play

cover_pdf = module._build_basic_pdf_bytes(
    "One Page Cover",
    {
        "title": "One Page Cover", "author": "Test Writer",
        "contact1": "Private and Confidential", "contact2": "Test Productions",
        "contact3": "writer@example.test", "contact4": "+44 0000 000000",
        "rights1": "All rights reserved", "rights2": "Copyright 2026",
    },
    [], "play", True, False,
).decode('latin-1')
assert len(re.findall(r'/Type /Page\b', cover_pdf)) == 1
for value in ('Private and Confidential', 'writer@example.test', 'All rights reserved', 'Copyright 2026'):
    assert value in cover_pdf

long_cover_pdf = module._build_basic_pdf_bytes(
    "A Complete Long Title Page",
    {
        "title": "THE EXTRAORDINARILY LONG TITLE OF A COMPLETE TESTER SCRIPT",
        "author": "Alexandra Example Writer and Christopher Example Writer",
        "basedOn": "Based on an original work with a deliberately detailed attribution line",
        "draft": "Complete Production Draft", "date": "13 July 2026",
        "contact1": "Private and Confidential Full Production Contact",
        "contact2": "Example Productions 123 Very Long Street Address London",
        "contact3": "alexandra.writer@example-production.test",
        "contact4": "+44 20 0000 0000",
        "rights1": "Copyright 2026 Alexandra Example Writer",
        "rights2": "All theatrical television and adaptation rights reserved",
    },
    [], "film", True, False,
).decode('latin-1')
assert len(re.findall(r'/Type /Page\b', long_cover_pdf)) == 1
for token in ('EXTRAORDINARILY', 'Christopher', 'attribution', 'Confidential',
              'Productions', 'alexandra.writer@example-', 'production.test',
              'Copyright', 'adaptation'):
    assert token in long_cover_pdf, token
print("BBC A4 PDF layout regression tests passed.")
