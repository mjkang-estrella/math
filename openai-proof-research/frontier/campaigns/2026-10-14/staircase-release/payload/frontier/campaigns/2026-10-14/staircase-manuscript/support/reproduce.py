#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Run frozen checker copies and a bounded retraction-interface control."""
import hashlib
import itertools
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def interface_control():
    # Literal q/content and translated-theta coordinates, independently evaluated.
    m = 2
    cells = [(1, 1), (1, 2), (2, 1)]
    beta = tuple(m + 2 - i - j for i, j in cells)
    b0 = tuple(j for i, j in cells)
    theta = (beta, b0, beta)
    w = tuple((m + 1 - i, m + 2 - i - j) for i, j in cells)
    desired = {(1, 1), (2, 1), (2, 2)}
    groups = list(itertools.permutations(range(3)))

    def act(a, g):
        out = [None] * 3
        for old, new in enumerate(g):
            out[new] = a[old]
        return tuple(out)

    basis = list(itertools.product(range(1, m + 1), repeat=3))
    cases = 0
    for a, b, c in itertools.product(basis, repeat=3):
        out = None
        if all(a[k] == c[k] for k in range(3)):
            trial = tuple((a[k] + b[k] - 1, a[k]) for k in range(3))
            if len(set(trial)) == 3 and set(trial) == desired:
                out = trial
        for g in groups:
            # [g e_w] pi q(x) versus theta*(g^{-1}x) = [g theta]x.
            projected_coordinate = int(out == act(w, g))
            functional_coordinate = int((a, b, c) == tuple(act(t, g) for t in theta))
            assert projected_coordinate == functional_coordinate
            cases += 1
    return {"m": m, "basis_triples": len(basis) ** 3, "group_elements": len(groups),
            "coordinate_comparisons": cases, "status": "PASS",
            "independent_review": False, "general_proof": False}


def main():
    if not __debug__:
        raise RuntimeError("Assertions must be enabled")
    checks = ROOT / "checks"
    checks.mkdir(exist_ok=True)
    runs = []
    with tempfile.TemporaryDirectory(prefix="run-work-", dir=checks) as folder:
        work = Path(folder)
        for name in ("proof_controls", "coordinate_controls"):
            original = ROOT / "support" / (name + ".py")
            copied = work / original.name
            shutil.copyfile(original, copied)
            process = subprocess.run([sys.executable, "-B", copied.name], cwd=work,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
            expected = (checks / ("expected-" + name + ".json")).read_bytes()
            assert process.returncode == 0, process.stderr.decode()
            assert process.stdout == expected, name + " differs from frozen expected output"
            # Retain a fresh run record without overwriting earlier runs.
            runs.append({"script": "support/" + original.name,
                         "command": ["python3", "-B", copied.name],
                         "execution_location": "temporary copy inside checks; removed after execution",
                         "script_sha256": sha(original.read_bytes()),
                         "expected_sha256": sha(expected), "stdout_sha256": sha(process.stdout),
                         "exit_code": process.returncode, "byte_identical": True,
                         "stderr": process.stderr.decode()})
    result = {"python": sys.version, "assertions_enabled": __debug__, "runs": runs,
              "interface_control": interface_control(),
              "finite_only": True, "fresh_independent_review_claimed": False, "status": "PASS"}
    (checks / "reproduction.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: two copied controls match complete frozen outputs; 3072 interface comparisons")


if __name__ == "__main__":
    main()
