from __future__ import annotations

import ast
import hashlib
import json
import re
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "frontier/experiments/i181_six_cycle_helper"
INVENTORY = BASE / "inventory.json"
OUT = BASE / "prevalidation.json"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def inventory_entries() -> list[dict]:
    inv = json.loads(INVENTORY.read_text(encoding="utf-8"))
    entries = inv["files"]
    if len({e["path"] for e in entries}) != len(entries):
        raise ValueError("duplicate inventory path")
    return entries


def authenticate_inventory() -> None:
    for entry in inventory_entries():
        path = ROOT / entry["path"]
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"missing or symbolic inventory file: {entry['path']}")
        if path.stat().st_size != entry["size"] or sha256(path) != entry["sha256"]:
            raise ValueError(f"inventory digest mismatch: {entry['path']}")


def syntax_and_links() -> dict:
    py_count = json_count = 0
    for entry in inventory_entries():
        path = ROOT / entry["path"]
        if path.suffix == ".py":
            ast.parse(path.read_bytes(), filename=str(path))
            py_count += 1
        elif path.suffix == ".json":
            json.loads(path.read_text(encoding="utf-8"))
            json_count += 1
    report = ROOT / "frontier/iterations/i181-six-cycle-helper.md"
    links = re.findall(r"\[[^\]]+\]\(([^)]+)\)", report.read_text(encoding="utf-8"))
    missing = []
    for link in links:
        if "://" in link or link.startswith("#"):
            continue
        target = (report.parent / link).resolve()
        if not target.exists():
            missing.append(link)
    if missing:
        raise ValueError(f"missing report links: {missing}")
    return {"python_files": py_count, "json_files": json_count, "report_links": len(links)}


STRICT = None


def read_json(relative: str):
    global STRICT
    if STRICT is None:
        frozen = json.loads((BASE / "inputs.json").read_bytes())
        STRICT = {row["path"]: row for row in frozen["strict"]}
    if not isinstance(relative, str) or relative.startswith("/") or ".." in relative.split("/"):
        raise AssertionError("unbound read")
    if relative not in STRICT:
        raise AssertionError("unbound read: " + relative)
    data = (ROOT / relative).read_bytes()
    row = STRICT[relative]
    assert len(data) == row["size"] and sha256_bytes(data) == row["sha256"]
    return json.loads(data)


def namespace() -> dict:
    env: dict = {"__name__": "i181_math"}
    data = (BASE / "math181.py").read_bytes()
    exec(compile(data, str(BASE / "math181.py"), "exec"), env)
    env = dict(env)
    env["read_json"] = read_json
    data = (BASE / "research181.py").read_bytes()
    exec(compile(data, str(BASE / "research181.py"), "exec"), env)
    return env


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def replay_twice() -> dict:
    result = {}
    for key in ("mandatory", "topology"):
        start = time.perf_counter()
        first = canonical(namespace()[key]())
        middle = time.perf_counter()
        second = canonical(namespace()[key]())
        end = time.perf_counter()
        if first != second:
            raise ValueError(f"non-identical double replay: {key}")
        retained_path = BASE / ("mandatory-attempt-05.json" if key == "mandatory" else "topology-attempt-01.json")
        retained = json.loads(retained_path.read_text(encoding="utf-8"))
        retained.pop("runtime_seconds", None)
        if first != canonical(retained):
            raise ValueError(f"replay differs from retained successful payload: {key}")
        result[key] = {
            "sha256": sha256_bytes(first),
            "size_without_runtime": len(first),
            "runtime_seconds": [middle - start, end - middle],
        }
    return result


def main() -> None:
    if (BASE / "seal.json").exists():
        raise RuntimeError("seal already exists; refusing prevalidation")
    authenticate_inventory()
    checks = syntax_and_links()
    result = {
        "package": "I181",
        "status": "PASS",
        "inventory_sha256": sha256(INVENTORY),
        "checks": checks,
        "diagnostics": replay_twice(),
    }
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"prevalidation": "PASS", "sha256": sha256(OUT)}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
