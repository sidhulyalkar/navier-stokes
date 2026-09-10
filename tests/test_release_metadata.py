import json
import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parents[1]


def project_version() -> str:
    text = (ROOT / "pyproject.toml").read_text()
    match = re.search(r'^version\s*=\s*"([^"]+)"', text, flags=re.MULTILINE)
    assert match is not None
    return match.group(1)


def test_release_validation_version_matches_package_version():
    validation = json.loads((ROOT / "RELEASE_VALIDATION.json").read_text())
    assert validation["version"] == project_version()


def test_source_lock_is_not_silently_migrated_by_upstream_watch():
    validation = json.loads((ROOT / "RELEASE_VALIDATION.json").read_text())
    source_lock = json.loads((ROOT / "SOURCE_LOCK.json").read_text())
    upstream = json.loads((ROOT / "UPSTREAM_WATCH.json").read_text())
    pinned = validation["source_policy"]["reproducibility_lock"]
    assert upstream["reproducibility_source_lock"] == pinned
    assert upstream["source_lock_changed"] is False
    serialized = json.dumps(source_lock)
    assert pinned in serialized
    assert upstream["observed_main"] != pinned
