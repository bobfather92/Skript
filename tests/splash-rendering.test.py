import ast
from pathlib import Path


SOURCE_PATH = Path(__file__).resolve().parents[1] / 'skript.py'
SOURCE = SOURCE_PATH.read_text(encoding='utf-8')
TREE = ast.parse(SOURCE)


def function_source(name):
    node = next(
        item for item in TREE.body
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)) and item.name == name
    )
    return ast.get_source_segment(SOURCE, node)


create_source = function_source('_create_splash')
pump_source = function_source('_pump_splash')
launch_source = function_source('launch')
destroy_source = function_source('_destroy_splash')
single_instance_source = function_source('_acquire_single_instance')

assert create_source.count('tk.Tk()') == 1, 'Splash must use one top-level widget'
assert "root.attributes('-alpha', 1.0)" in create_source, 'Splash must be fully opaque'
assert "root.attributes('-alpha', 0.97)" not in create_source
assert 'for step in range(18, 0, -1)' not in create_source, 'Layered vignette caused background bands'
assert "root.geometry(f'{W}x{H}+{splash_x}+{splash_y}')" in create_source, \
    'Splash must be a compact centred window'
assert "root.geometry(f'{sw}x{sh}+0+0')" not in create_source, \
    'A full-screen topmost splash can leave stale graphics surfaces'
assert create_source.count('tk.Canvas(') == 1, 'Splash must contain one loading card'
assert "main.pack(fill='both', expand=True)" in create_source
assert "main.place(relx=0.5, rely=0.5, anchor='center')" not in create_source
assert "splash.withdraw()" in destroy_source
assert "DwmFlush" in destroy_source
assert "_destroy_splash(splash)" in launch_source

assert launch_source.count('_create_splash()') == 1, 'Launch must create one splash instance'
assert 'CreateMutexW' in single_instance_source, 'Windows launches must use a singleton mutex'
assert launch_source.index('_acquire_single_instance()') < launch_source.index('_create_splash()'), \
    'Singleton guard must run before the splash is created'
assert 'Jake McNeil - 2026' in create_source
assert "Jake's Own Films Productions" not in create_source
assert "_resource_path('VERSION.txt')" in create_source, \
    'The loading splash must read the packaged release version'
for spec_name in ('Skript.spec', 'SkriptDiagnostic.spec'):
    spec_source = (SOURCE_PATH.parent / spec_name).read_text(encoding='utf-8')
    assert "project_root / 'VERSION.txt'" in spec_source, \
        f'{spec_name} must package VERSION.txt for the loading splash'
get_html_source = function_source('_get_html')
assert "injection.find('#sf-boot-screen {')" in get_html_source
assert "injection = injection[:boot_start] + '</style>'" in get_html_source, \
    'Low-performance mode must strip the redundant browser splash'
assert 'create_rectangle' not in pump_source
assert 'create_oval' not in pump_source
assert 'create_polygon' not in pump_source
assert 'c.coords(splash._sf_bar_fill' in pump_source
assert 'c.coords(splash._sf_shimmer' in pump_source

print('Splash rendering lifecycle regression tests passed.')
