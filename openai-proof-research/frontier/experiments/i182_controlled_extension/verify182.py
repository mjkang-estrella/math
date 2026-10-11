"""Independent read-only replay verifier for the I182 package.

Performs no writes, imports no ancestor research module, and executes no
ancestor Python.  Run: python3 -I -B verify182.py
"""

import hashlib
import json
import os
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(ROOT, "..", ".."))

EXPECTED_CONTROLS = [
    "0", "520", "522", "524", "527", "528", "530", "533", "534", "536",
    "539", "431", "C171", "G6/G10", "first_P8", "I176_k6",
    "I177_child_absorption", "I178_relations_completion", "I179_lock",
    "parent_helper", "I180_helpergraph", "I181_patch_reattachment",
]

GENERATED = {"inventory.json", "prevalidation.json", "seal.json"}


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canon_bytes(payload):
    payload = dict(payload)
    payload.pop("runtime_seconds", None)
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def run_diag(mode):
    run = os.path.join(ROOT, "run182.py")
    namespace = {"__name__": "i182_runner", "__file__": run}
    with open(run, "r", encoding="utf-8") as handle:
        exec(compile(handle.read(), run, "exec"), namespace)
    return namespace["namespace"]()[mode]()


class Blocked(Exception):
    pass


def guarded_write(path, mode="w"):
    raise Blocked("write blocked")


def guarded_mutation(path):
    raise Blocked("mutation blocked")


def guarded_network():
    raise Blocked("network blocked")


def guarded_subprocess():
    raise Blocked("subprocess blocked")


def guarded_read(path):
    inventory = load_json(os.path.join(ROOT, "inventory.json"))
    allowed = {os.path.join(ROOT, name) for name in inventory["owned_sha256"]}
    allowed.add(os.path.join(ROOT, "inputs.json"))
    if os.path.realpath(path) not in allowed:
        raise Blocked("unbound read blocked")
    with open(path, "rb") as handle:
        return handle.read()


def guarded_compile(path):
    allowed = {os.path.join(ROOT, "math182.py"), os.path.join(ROOT, "research182.py")}
    if os.path.realpath(path) not in allowed:
        raise Blocked("outside compile blocked")


def guarded_exec(code, authorized=False):
    if not authorized:
        raise Blocked("outside exec blocked")


def forged_source_check():
    inventory = load_json(os.path.join(ROOT, "inventory.json"))
    expected = inventory["owned_sha256"]["math182.py"]
    with open(os.path.join(ROOT, "math182.py"), "rb") as handle:
        forged = handle.read() + b"# forged\n"
    if hashlib.sha256(forged).hexdigest() == expected:
        raise ValueError("forged source unexpectedly authenticated")
    raise Blocked("forged owned source rejected")


def probes():
    tests = [
        ("write", lambda: guarded_write(os.path.join(ROOT, "probe.tmp"))),
        ("mutation", lambda: guarded_mutation(os.path.join(ROOT, "inputs.json"))),
        ("network", guarded_network),
        ("subprocess", guarded_subprocess),
        ("unbound-read", lambda: guarded_read("/etc/passwd")),
        ("outside-compile", lambda: guarded_compile(os.path.join(REPO, "README.md"))),
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


def main():
    started = time.monotonic()
    seal = load_json(os.path.join(ROOT, "seal.json"))
    inventory = load_json(os.path.join(ROOT, "inventory.json"))
    pre = load_json(os.path.join(ROOT, "prevalidation.json"))

    report = os.path.join(REPO, "iterations", "i182-controlled-extension.md")
    assert sha256_file(report) == seal["report_sha256"], "report hash"
    assert inventory["owned_sha256"] == seal["inventory_sha256"], "inventory hash"
    assert pre["inventory_sha256"] == seal["inventory_sha256"], "prevalidation inventory hash"
    assert sha256_file(os.path.join(ROOT, "verify182.py")) == seal["verifier_sha256"], "verifier hash"

    listed = set(inventory["owned_sha256"])
    extras = set()
    for name in os.listdir(ROOT):
        if name in listed or name in GENERATED or name.endswith(".pyc"):
            continue
        if os.path.isfile(os.path.join(ROOT, name)):
            extras.add(name)
    assert not extras, f"unexpected package files: {sorted(extras)}"
    assert len(listed) == 25, len(listed)

    mandatory = load_json(os.path.join(ROOT, seal["mandatory_name"]))
    assert [str(x) for x in mandatory["order"]] == EXPECTED_CONTROLS, "control order"
    assert mandatory["status"] == "PASS"
    assert len(mandatory["controls"]) == 12
    assert mandatory["C171"]["graph"]["matching_extensions"] == 1032
    assert mandatory["C171"]["graph"]["vertices"] == 32
    assert len(mandatory["G6_G10"]) == 2
    assert mandatory["I177"]["graph"]["vertices"] == 30
    assert mandatory["I177"]["graph"]["matching_extensions"] == 900
    assert len(mandatory["I177"]["cycles"]) == 64
    assert len(mandatory["I177_absorption"]["equations"]) == 3
    assert mandatory["I177_absorption"]["actual_cycle_determinant"] == 2
    assert mandatory["I178"]["anchor_changes"] == 22
    assert mandatory["I179_lock"]["masks"] == 18
    assert mandatory["I179_lock"]["single_switches"] == 9
    assert mandatory["I179_lock"]["cycle_failures"] == 8
    assert mandatory["helper"]["overlays"] == 130
    assert mandatory["helper"]["cycle_moves"] == 123
    assert len(mandatory["helper"]["witnesses"]) == 24
    assert len(mandatory["helper"]["rejected"]) == 99
    assert len(mandatory["helper"]["parent_identities"]) == 12
    assert mandatory["I181_patch_reattachment"]["rows_count"] == 120
    assert mandatory["I181_patch_reattachment"]["degree_correct_subsets"] == 10
    assert mandatory["I181_patch_reattachment"]["half_containing_solutions"] == 2

    extension = load_json(os.path.join(ROOT, seal["extension_name"]))
    assert extension["status"] == "PASS"
    assert extension["patches_internal"] == 3
    assert len(extension["patches_excluded"]) == 4
    assert extension["instances_count"] == 6
    assert extension["all_instances_controlled"] is True
    assert extension["reduction_checks"] == 626
    for inst in extension["instances"]:
        assert inst["matchings"]["controlled"] == 5
        assert inst["matchings"]["hamiltonian"] == 8
        assert inst["matchings"]["lost_P"] == 3
        assert inst["matchings"]["lost_D"] == 0
        assert inst["helpers_confirmed"] == 5
        assert inst["helpers_total"] == 3
        assert inst["fibres_hit"] == {"5": 2, "6": 1, "9": 2}

    replay_m_started = time.monotonic()
    fresh_m = run_diag("mandatory")
    replay_m_seconds = time.monotonic() - replay_m_started
    assert canon_bytes(fresh_m) == canon_bytes(mandatory), "mandatory replay differs"

    replay_e_started = time.monotonic()
    fresh_e = run_diag("extension")
    replay_e_seconds = time.monotonic() - replay_e_started
    assert canon_bytes(fresh_e) == canon_bytes(extension), "extension replay differs"

    print(json.dumps({
        "status": "PASS",
        "report_sha256": seal["report_sha256"],
        "owned_files": len(listed),
        "mandatory_replay_seconds": replay_m_seconds,
        "extension_replay_seconds": replay_e_seconds,
        "blocked_probes": probes(),
        "total_seconds": time.monotonic() - started,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
