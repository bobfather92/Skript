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
        {"type": "new-act", "text": "ACT TWO"},
    ],
    "film",
    False,
    True,
)

expected_css = [
    "margin: 1in 0.75in 1in 1.5in",
    'content: counter(page) "."',
    "counter-increment: page 0",
    "@bottom-left { content: none; }",
    "@bottom-center { content: none; }",
    "@bottom-right { content: none; }",
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
assert 'text-align: right' in transition_css
assert 'class="el-new-act">ACT TWO</div>' in html
new_act_css = html.split('.el-new-act', 1)[1].split('}', 1)[0]
assert 'text-align: center' in new_act_css
assert 'text-decoration: underline' in new_act_css
assert "border-top" not in new_act_css
page_stamp_css = html.split(".page-num-stamp {", 1)[1].split("}", 1)[0]
assert "display: none" in page_stamp_css

fallback_source = (ROOT / 'skript.py').read_text(encoding='utf-8')
assert "transition_x = max(left_default, page_w - 54" in fallback_source
assert "elif typ == 'new-act':" in fallback_source
assert "if getattr(sys, 'frozen', False):" not in fallback_source.split(
    "elif path == '/api/export-pdf':", 1
)[1].split("# ── Molly AI proxy", 1)[0]
assert "'renderer': 'basic'" in fallback_source

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

notes_excluded = module._build_pdf_html(
    "Notes Choice", {}, [
        {"type": "action", "text": "Visible action."},
        {"type": "notes", "text": "Private note."},
    ], "film", False, True,
)
assert "Visible action." in notes_excluded
assert "Private note." not in notes_excluded
notes_included = module._build_pdf_html(
    "Notes Choice", {}, [
        {"type": "action", "text": "Visible action."},
        {"type": "notes", "text": "Included note."},
    ], "film", False, True, None, True,
)
assert 'class="el-notes">Included note.</div>' in notes_included

radio = module._build_pdf_html(
    "Radio Test", {}, [
        {"type": "scene", "text": "SCENE 1."},
        {"type": "action", "text": "SFX: A DOOR CLOSES."},
        {"type": "character", "text": "MAYA"},
        {"type": "parenthetical", "text": "(close)"},
        {"type": "dialogue", "text": "We are on air."},
    ], "audio", False, True,
)
assert '<body class="format-audio">' in radio
assert '@page radio' in radio
assert 'font-family: Arial, Helvetica, sans-serif' in radio
assert '.format-audio .el-character::after { content: ":"; }' in radio
assert 'content: "- " counter(page) " -"' in radio
assert 'class="radio-speech"' in radio
assert 'class="radio-cue">MAYA:</div>' in radio
assert 'class="radio-parenthetical">(close)</span>' in radio
assert 'class="radio-dialogue">We are on air.</span>' in radio

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

fallback_layout_pdf = module._build_basic_pdf_bytes(
    "Fallback Layout",
    {},
    [],
    "film",
    False,
    True,
    [
        {"type": "new-act", "text": "ACT ONE"},
        {"type": "transition", "text": "FADE IN:"},
        {"type": "scene", "text": "EXT. LOCATION - DAY"},
        {"type": "action", "text": "The first page follows BBC spacing."},
        {"type": "character", "text": "MAYA"},
        {"type": "dialogue", "text": "This speech continues."},
        {"type": "_more", "text": "(MORE)"},
        {"type": "_break", "text": ""},
        {"type": "_page-num", "text": "2."},
        {"type": "_contd", "text": "MAYA (CONT'D)"},
        {"type": "dialogue", "text": "On a genuine second page."},
        {"type": "transition", "text": "CUT TO:"},
        {"type": "new-act", "text": "ACT TWO"},
        {"type": "scene", "text": "INT. SECOND LOCATION - NIGHT"},
    ],
).decode("latin-1")

# Explicit editor pagination must remain structural in the dependency-free
# renderer. Markers must never print as ordinary body text.
assert len(re.findall(r"/Type /Page\b", fallback_layout_pdf)) == 3
assert "_break" not in fallback_layout_pdf
assert "_page-num" not in fallback_layout_pdf
assert re.search(r"252\.00 \d+\.\d+ Td \(\\\(MORE\\\)\)", fallback_layout_pdf)
assert re.search(r"487\.28 793\.89 Td \(2\.\)", fallback_layout_pdf)
assert re.search(r"487\.28 793\.89 Td \(1\.\)", fallback_layout_pdf)
assert re.search(r"487\.28 793\.89 Td \(3\.\)", fallback_layout_pdf)
assert "MAYA \\(CONT'D\\)" in fallback_layout_pdf
assert not re.search(r"\b(?:http|file):", fallback_layout_pdf, re.I)

# The first Act, transition, scene and action use the same 12pt line grid as
# the BBC reference: 36pt from Act to transition, then 24pt between blocks.
assert "272.44 758.00 Td (ACT ONE)" in fallback_layout_pdf
assert "483.68 722.00 Td (FADE IN:)" in fallback_layout_pdf
assert "108.00 698.00 Td (EXT. LOCATION - DAY)" in fallback_layout_pdf
assert "108.00 674.00 Td (The first page follows BBC spacing.)" in fallback_layout_pdf
print("BBC A4 PDF layout regression tests passed.")
