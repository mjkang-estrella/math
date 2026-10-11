"""Fresh I182 package inventory."""

import json
import os

ROOT = os.path.dirname(os.path.abspath(__file__))
INVENTORY = os.path.join(ROOT, "inventory.json")


def main():
    auth = os.path.join(ROOT, "auth182.py")
    namespace = {"__name__": "i182_auth", "__file__": auth}
    with open(auth, "r", encoding="utf-8") as handle:
        exec(compile(handle.read(), auth, "exec"), namespace)
    namespace["frozen_check"]()

    frozen = namespace["load"](os.path.join(ROOT, "inputs.json"))
    files = []
    for name in sorted(os.listdir(ROOT)):
        if name in ("inventory.json", "__pycache__") or name.endswith(".pyc"):
            continue
        path = os.path.join(ROOT, name)
        if not os.path.isfile(path):
            continue
        files.append({"name": name,
                      "bytes": os.path.getsize(path),
                      "sha256": namespace["sha"](path)})

    output = {
        "iteration": 182,
        "base_iteration": 181,
        "verdict": "E182 UNRESOLVED",
        "owned_files": len(files),
        "strict_bound_files": len(frozen["strict"]),
        "context_bound_files": len(frozen.get("context", [])),
        "files": files,
        "owned_sha256": {row["name"]: row["sha256"] for row in files},
    }
    tmp = INVENTORY + ".tmp"
    with open(tmp, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(tmp, INVENTORY)
    print(json.dumps({"status": "PASS", "files": len(files)}))


if __name__ == "__main__":
    main()
