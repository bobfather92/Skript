import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("skript_folder_migration", ROOT / "skript.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


with tempfile.TemporaryDirectory(dir=ROOT / "tmp") as temp_dir:
    home = Path(temp_dir)
    legacy = home / "Documents" / ("Script" + "Forge")
    legacy_scripts = legacy / "scripts"
    legacy_userdata = legacy / "userdata"
    legacy_scripts.mkdir(parents=True)
    legacy_userdata.mkdir(parents=True)

    project = legacy_scripts / "Legacy Film.script"
    project.write_text('{"title":"Legacy Film","lines":[]}', encoding="utf-8")
    backup = legacy_scripts / "Legacy Film.script.bak1"
    backup.write_text('{"title":"Legacy Film backup","lines":[]}', encoding="utf-8")
    collision = legacy_scripts / "Existing.script"
    collision.write_text("legacy must remain", encoding="utf-8")
    recovery = legacy_userdata / "recovery.recover"
    recovery.write_text(
        '{"schema":"com.skript.workspace-recovery","projects":[]}', encoding="utf-8"
    )
    (legacy_userdata / "recent_scripts.json").write_text(
        json.dumps(
            [
                {"path": str(project), "title": "Legacy Film"},
                {"path": str(collision), "title": "Legacy collision"},
            ]
        ),
        encoding="utf-8",
    )

    new_collision = home / "Documents" / "Skript" / "scripts" / "Existing.script"
    new_collision.parent.mkdir(parents=True)
    new_collision.write_text("new file wins", encoding="utf-8")
    legacy_hashes = {path: digest(path) for path in (project, backup, collision, recovery)}

    userdata, scripts = module._app_dirs(home=home)

    assert scripts == home / "Documents" / "Skript" / "scripts"
    assert userdata == home / "Documents" / "Skript" / "userdata"
    assert (scripts / project.name).read_bytes() == project.read_bytes()
    assert (scripts / backup.name).read_bytes() == backup.read_bytes()
    assert new_collision.read_text(encoding="utf-8") == "new file wins"
    assert (userdata / recovery.name).read_bytes() == recovery.read_bytes()
    assert (userdata / ".skript-migration-complete").is_file()

    recent = json.loads((userdata / "recent_scripts.json").read_text("utf-8"))
    assert recent[0]["path"] == str(scripts / project.name)
    assert recent[1]["path"] == str(collision), "A colliding legacy project must keep its original path"

    for path, expected_hash in legacy_hashes.items():
        assert path.is_file()
        assert digest(path) == expected_hash, f"Migration changed legacy file: {path.name}"

print("Earlier project folders migrate safely into Documents/Skript.")
