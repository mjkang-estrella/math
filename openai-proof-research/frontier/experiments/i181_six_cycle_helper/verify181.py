from __future__ import annotations

import hashlib
import json
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "frontier/experiments/i181_six_cycle_helper"
REPORT = ROOT / "frontier/iterations/i181-six-cycle-helper.md"
INVENTORY = BASE / "inventory.json"
PREVALIDATION = BASE / "prevalidation.json"
SEAL = BASE / "seal.json"
VERIFIER = Path(__file__).resolve()
INPUTS = BASE / "inputs.json"

EXPECTED_CONTROLS = [
    0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539,
    431, "C171", "G6/G10", "first_P8", "I176_k6", "I177_child_absorption",
    "I178_relations_completion", "I179_lock", "parent_helper", "I180_helpergraph",
]


class Blocked(RuntimeError):
    pass


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def authenticate_package() -> dict:
    seal = load_json(SEAL)
    inventory = load_json(INVENTORY)
    prevalidation = load_json(PREVALIDATION)
    checks = {
        "report": sha256(REPORT) == seal["report_sha256"],
        "inventory": sha256(INVENTORY) == seal["inventory_sha256"],
        "prevalidation": sha256(PREVALIDATION) == seal["prevalidation_sha256"],
        "verifier": sha256(VERIFIER) == seal["verifier_sha256"],
        "prevalidation_status": prevalidation.get("status") == "PASS",
        "inventory_file_count": len(inventory["files"]) == seal["inventory_file_count"],
    }
    for entry in inventory["files"]:
        path = ROOT / entry["path"]
        checks[f"file:{entry['path']}"] = (
            path.is_file()
            and not path.is_symlink()
            and path.stat().st_size == entry["size"]
            and sha256(path) == entry["sha256"]
        )
    if not all(checks.values()):
        bad = [key for key, ok in checks.items() if not ok]
        raise ValueError(f"package authentication failed: {bad}")
    return {"seal": seal, "inventory": inventory, "checks": len(checks)}


def integrity_state() -> bytes:
    inputs = load_json(INPUTS)
    strict_rows = inputs["strict"]
    strict = {row["path"]: row for row in strict_rows}
    if len(strict) != len(strict_rows):
        raise ValueError("duplicate strict binding")
    state = {
        "strict": {},
        "contexts": {},
        "membership": {},
        "ancestor_chains": inputs["ancestor_chains"],
        "control_order": load_json(BASE / "mandatory-attempt-05.json")["order"],
    }
    for path, row in sorted(strict.items()):
        current = ROOT / path
        state["strict"][path] = (
            current.is_file()
            and current.stat().st_size == row["size"]
            and sha256(current) == row["sha256"]
        )
    for item in inputs["context"]:
        path = item["path"]
        current = ROOT / path
        state["contexts"][path] = (
            current.is_file()
            and current.stat().st_size == item["size"]
            and sha256(current) == item["sha256"]
        )
    for path in inputs["parent_membership"]:
        row = strict.get(path)
        current = ROOT / path
        state["membership"][path] = (
            row is not None
            and current.is_file()
            and current.stat().st_size == row["size"]
            and sha256(current) == row["sha256"]
        )
    if not all(state["strict"].values()):
        raise ValueError("strict binding changed")
    if not all(state["contexts"].values()):
        raise ValueError("current context changed")
    if not all(state["membership"].values()):
        raise ValueError("parent membership binding changed")
    if not all(chain.get("control_chain") for chain in inputs["ancestor_chains"]):
        raise ValueError("ancestor control chain changed")
    if state["control_order"] != EXPECTED_CONTROLS:
        raise ValueError("control order changed")
    return canonical(state)


STRICT = None


def read_json(relative: str):
    global STRICT
    if STRICT is None:
        frozen = load_json(INPUTS)
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
    inventory = load_json(INVENTORY)
    expected = {entry["path"]: entry["sha256"] for entry in inventory["files"]}
    env: dict = {"__name__": "i181_math"}
    path = BASE / "math181.py"
    data = path.read_bytes()
    rel = path.relative_to(ROOT).as_posix()
    if expected.get(rel) != sha256_bytes(data):
        raise ValueError("owned source authentication failed: math181.py")
    exec(compile(data, str(path), "exec"), env)
    env = dict(env)
    env["read_json"] = read_json
    path = BASE / "research181.py"
    data = path.read_bytes()
    rel = path.relative_to(ROOT).as_posix()
    if expected.get(rel) != sha256_bytes(data):
        raise ValueError("owned source authentication failed: research181.py")
    exec(compile(data, str(path), "exec"), env)
    return env


def replay(name: str, retained_name: str) -> dict:
    start = time.perf_counter()
    first = canonical(namespace()[name]())
    middle = time.perf_counter()
    second = canonical(namespace()[name]())
    end = time.perf_counter()
    if first != second:
        raise ValueError(f"non-identical double replay: {name}")
    retained = load_json(BASE / retained_name)
    retained.pop("runtime_seconds", None)
    if first != canonical(retained):
        raise ValueError(f"retained payload mismatch: {name}")
    return {
        "sha256": sha256_bytes(first),
        "bytes_without_runtime": len(first),
        "runtime_seconds": [middle - start, end - middle],
    }


def guarded_write(path: Path, mode: str) -> None:
    if any(flag in mode for flag in "wax+"):
        raise Blocked("write blocked")


def guarded_mutation(path: Path) -> None:
    raise Blocked("mutation blocked")


def guarded_network() -> None:
    raise Blocked("network blocked")


def guarded_subprocess() -> None:
    raise Blocked("subprocess blocked")


def guarded_read(path: Path) -> bytes:
    allowed = {ROOT / entry["path"] for entry in load_json(INVENTORY)["files"]}
    allowed.add(INPUTS)
    if path.resolve() not in allowed:
        raise Blocked("unbound read blocked")
    return path.read_bytes()


def guarded_compile(path: Path) -> None:
    allowed = {BASE / "math181.py", BASE / "research181.py"}
    if path.resolve() not in allowed:
        raise Blocked("outside compile blocked")


def guarded_exec(code: str, authorized: bool = False) -> None:
    if not authorized:
        raise Blocked("outside exec blocked")


def forged_source_check() -> None:
    inventory = load_json(INVENTORY)
    expected = {entry["path"]: entry["sha256"] for entry in inventory["files"]}
    rel = (BASE / "math181.py").relative_to(ROOT).as_posix()
    forged = (BASE / "math181.py").read_bytes() + b"# forged\n"
    if sha256_bytes(forged) == expected[rel]:
        raise ValueError("forged source unexpectedly authenticated")
    raise Blocked("forged owned source rejected")


def probes() -> list[dict]:
    outside = ROOT / "README.md"
    tests = [
        ("write", lambda: guarded_write(BASE / "probe.tmp", "w")),
        ("mutation", lambda: guarded_mutation(BASE / "inputs.json")),
        ("network", guarded_network),
        ("subprocess", guarded_subprocess),
        ("unbound-read", lambda: guarded_read(Path("/etc/passwd"))),
        ("outside-compile", lambda: guarded_compile(outside)),
        ("outside-exec", lambda: guarded_exec("print('blocked')")),
        ("forged-owned-source", forged_source_check),
    ]
    result = []
    for name, fn in tests:
        try:
            fn()
        except Blocked as exc:
            result.append({"probe": name, "status": "BLOCKED", "detail": str(exc)})
        else:
            raise ValueError(f"probe was not blocked: {name}")
    return result


def main() -> None:
    package = authenticate_package()
    before = integrity_state()
    mandatory = replay("mandatory", "mandatory-attempt-05.json")
    topology = replay("topology", "topology-attempt-01.json")
    after = integrity_state()
    if before != after:
        raise ValueError("strict/context/membership/control state changed during replay")
    receipt = {
        "package": "I181",
        "status": "PASS",
        "E181": "UNRESOLVED",
        "package_checks": package["checks"],
        "report_sha256": package["seal"]["report_sha256"],
        "inventory_sha256": package["seal"]["inventory_sha256"],
        "prevalidation_sha256": package["seal"]["prevalidation_sha256"],
        "verifier_sha256": package["seal"]["verifier_sha256"],
        "seal_sha256": sha256(SEAL),
        "mandatory_replay": mandatory,
        "topology_replay": topology,
        "blocked_probes": probes(),
        "integrity_state": "UNCHANGED",
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
