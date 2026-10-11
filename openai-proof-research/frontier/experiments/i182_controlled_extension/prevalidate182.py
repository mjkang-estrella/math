"""Fresh I182 prevalidation: byte-identical double replay."""

import hashlib
import json
import os

ROOT = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(ROOT, "prevalidation.json")


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def runner_namespace():
    run = os.path.join(ROOT, "run182.py")
    namespace = {"__name__": "i182_runner", "__file__": run}
    with open(run, "r", encoding="utf-8") as handle:
        exec(compile(handle.read(), run, "exec"), namespace)
    return namespace


def run_diag(mode):
    return runner_namespace()["namespace"]()[mode]()


def canon_bytes(payload):
    payload = dict(payload)
    payload.pop("runtime_seconds", None)
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def main():
    mandatory = os.path.join(ROOT, "mandatory-attempt-05.json")
    extension = os.path.join(ROOT, "extension-attempt-01.json")
    retained_m = canon_bytes(load_json(mandatory))
    retained_e = canon_bytes(load_json(extension))
    checks = {}
    for label, mode, retained in (
        ("mandatory_replay_1", "mandatory", retained_m),
        ("mandatory_replay_2", "mandatory", retained_m),
        ("extension_replay_1", "extension", retained_e),
        ("extension_replay_2", "extension", retained_e),
    ):
        fresh = canon_bytes(run_diag(mode))
        checks[label] = {"byte_identical": fresh == retained,
                         "sha256": hashlib.sha256(fresh).hexdigest()}
        assert fresh == retained, label

    inventory = load_json(os.path.join(ROOT, "inventory.json"))
    output = {
        "iteration": 182,
        "base_iteration": 181,
        "report_name": "i182-controlled-extension.md",
        "seal_intended_name": "seal.json",
        "verifier_name": "verify182.py",
        "runner_name": "run182.py",
        "mandatory_name": os.path.basename(mandatory),
        "mandatory_payload_sha256": sha256_file(mandatory),
        "extension_name": os.path.basename(extension),
        "extension_payload_sha256": sha256_file(extension),
        "inventory_sha256": inventory["owned_sha256"],
        "checks": checks,
        "status": "PASS",
    }
    tmp = OUT + ".tmp"
    with open(tmp, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(tmp, OUT)
    print(json.dumps({"status": "PASS",
                      "checks": {k: v["byte_identical"] for k, v in checks.items()}}))


if __name__ == "__main__":
    main()
