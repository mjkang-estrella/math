"""Fresh I182 one-attempt exclusive seal."""

import hashlib
import json
import os

ROOT = os.path.dirname(os.path.abspath(__file__))
REPORT = os.path.abspath(os.path.join(ROOT, "..", "..", "iterations", "i182-controlled-extension.md"))


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def main():
    pre = load_json(os.path.join(ROOT, "prevalidation.json"))
    assert pre["status"] == "PASS"
    inventory = load_json(os.path.join(ROOT, "inventory.json"))
    seal = {
        "iteration": 182,
        "base_iteration": 181,
        "report_path": os.path.relpath(REPORT, os.path.dirname(ROOT)),
        "report_sha256": sha256_file(REPORT),
        "package_dir": os.path.basename(ROOT),
        "mandatory_name": pre["mandatory_name"],
        "mandatory_payload_sha256": pre["mandatory_payload_sha256"],
        "extension_name": pre["extension_name"],
        "extension_payload_sha256": pre["extension_payload_sha256"],
        "inventory_sha256": {k: inventory["owned_sha256"][k] for k in sorted(inventory["owned_sha256"])},
        "verifier_name": pre["verifier_name"],
        "verifier_sha256": sha256_file(os.path.join(ROOT, pre["verifier_name"])),
        "verifier_command": "python3 -I -B verify182.py",
        "package_scope": "I182-only; no ancestor files are claimed",
        "status": "PASS",
    }
    path = os.path.join(ROOT, "seal.json")
    with open(path, "x", encoding="utf-8") as handle:
        json.dump(seal, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps({"status": "PASS", "seal_sha256": sha256_file(path)}))


if __name__ == "__main__":
    main()
