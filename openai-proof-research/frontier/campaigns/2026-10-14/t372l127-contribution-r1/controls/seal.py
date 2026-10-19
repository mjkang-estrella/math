#!/usr/bin/env python3
"""Build MANIFEST.json and FINAL.json for the T372L127 contribution review r1.

Usage: python3 controls/seal.py            (writes MANIFEST.json then FINAL.json in the review root)
The excluded set must equal the fixed set in public/verify.py.
"""
import hashlib, json, os, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AUTHOR_ROOT = os.path.join(os.path.dirname(ROOT), "fresh-analytic-discovery-r127")
EXCLUDED = ["FINAL.json", "REPORT.md", "MANIFEST.json", "controls/receipt.json"]
TEMP_PREFIX = "controls/tmp-"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"

AUTHOR_ANCHOR_FILES = [
    "FINAL.json", "REPORT.md", "packet/MANIFEST.json", "controls/receipt.json",
    "packet/public/frozen-scope.md", "packet/public/freeze.json", "packet/public/proof.md",
    "packet/public/transport-calculation.md", "packet/public/boundary-calculation.md",
    "packet/public/consistency-check.md", "packet/public/report.md", "packet/public/reading-limits.md",
    "packet/public/prefreeze.md", "packet/public/other-screens.md", "packet/public/verify.py",
]
BRIEF_ANCHORS = {  # the six anchors stated in contribution-review-brief.txt
    "FINAL.json": "bf1f7e54da87fa799201fa78c30a45bec7fdee6631ff14e9aaf78f66aa30c15f",
    "REPORT.md": "97d95dbb2fca982fec5e09fbb64409e296ca6889088693967a04761105cc0e86",
    "packet/MANIFEST.json": "a48867c451ac1ebf79fc6fdf38472a7a39873f6346620f305a9e43c1e0b65af3",
    "packet/public/frozen-scope.md": "6e39d59e65aecf9fc8710244c7eccbe7964e38af10287ad173663585539d790a",
    "packet/public/proof.md": "a1831655de6307324476184d9a208d212de5b366a9c939fdcdacb9fadf974e6c",
    "controls/receipt.json": "3496fe34cc3c13bc578cdcc2889b909727563915ec452a7e390292c4e84cfc7a",
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def build_manifest(root):
    payloads = {}
    for dp, dns, fns in os.walk(root):
        rel_dir = os.path.relpath(dp, root)
        dns[:] = sorted(d for d in dns if not os.path.join(rel_dir, d).replace("\\", "/").lstrip("./").startswith(TEMP_PREFIX))
        for fn in sorted(fns):
            rel = os.path.normpath(os.path.join(rel_dir, fn)).replace("\\", "/")
            if rel.startswith("./"):
                rel = rel[2:]
            if rel in EXCLUDED:
                continue
            p = os.path.join(dp, fn)
            payloads[rel] = {"sha256": sha256(p), "bytes": os.path.getsize(p)}
    return {
        "task": "T372L127 contribution review r1",
        "excluded": EXCLUDED,
        "excluded_note": "FINAL.json and REPORT.md are anchored by DETACHED hashes published in the final message; "
                         "MANIFEST.json is anchored by FINAL.json; controls/receipt.json is written after sealing.",
        "payload_count": len(payloads),
        "payloads": payloads,
    }


def main():
    man = build_manifest(ROOT)
    man_p = os.path.join(ROOT, "MANIFEST.json")
    with open(man_p, "w", encoding="utf-8") as f:
        json.dump(man, f, indent=1, sort_keys=True)
        f.write("\n")
    anchors = {}
    for rel in AUTHOR_ANCHOR_FILES:
        anchors[rel] = sha256(os.path.join(AUTHOR_ROOT, rel))
    brief_match = {k: anchors[k] == v for k, v in BRIEF_ANCHORS.items()}
    if not all(brief_match.values()):
        sys.stderr.write("brief anchors do not match: %s\n" % brief_match)
        return 1
    final = {
        "task": "analytic r127 T372L127 contribution review r1",
        "task_id": "node:delegated-task:command%3Amcp%3A80f6ec49-twenty-20261019-t372l127-contribution-factory-r1",
        "role": "independent CONTRIBUTION review sub-agent (does not inspect the proof review or its brief)",
        "runner": "Factory Droid (Claude Fable 5.1)",
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "pin": PIN,
        "claim_reviewed": "Full original T372L127: uniform logarithmic stability of both Lame coefficients (lambda, mu) "
                          "from the full Dirichlet-to-Neumann map, no boundary agreement assumed, constants depending "
                          "only on Omega, c, M; stipulated-true source372 uniqueness at the pin.",
        "verdict": "TECHNICAL",
        "conditional_on_correctness": True,
        "verdict_meaning": "New-to-project and (as far as searched) new-to-literature, but obtainable by a routine "
                           "Alessandrini-type quantification of the stipulated source372 uniqueness argument; the "
                           "structural bridge is the source's and the quantitative increment uses generic estimates.",
        "strongest_compatible_reduction": "public/generic-reduction.md (Q1-Q8) + public/literature-comparison.md",
        "rediscovered_excluded_because": "No prior log (or any) stability statement for both Lame coefficients from the "
                                         "full DN map without smallness/finite-dimensional hypotheses was found; "
                                         "uniqueness itself was open until the pinned source and arXiv:2610.14741v1.",
        "manifest_sha256": sha256(man_p),
        "manifest_payload_count": man["payload_count"],
        "author_input_root": "../fresh-analytic-discovery-r127",
        "author_input_anchors": {"files": anchors, "brief_anchor_match": brief_match},
        "detached_anchors": "SHA256 of FINAL.json and REPORT.md are published only in the final message, not stored here.",
        "verifier": "public/verify.py (own, read-only, requires detached FINAL and REPORT hashes)",
        "controls": "controls/run_controls.py -> controls/receipt.json (disposable copies under controls/tmp-*, originals hashed before/after)",
        "no_self_count": True,
        "no_acceptance_claim": True,
        "no_priority_claim": True,
        "artifact_checks_are_mathematical_gates": False,
    }
    final_p = os.path.join(ROOT, "FINAL.json")
    with open(final_p, "w", encoding="utf-8") as f:
        json.dump(final, f, indent=1, sort_keys=True)
        f.write("\n")
    print(json.dumps({"MANIFEST.json": sha256(man_p), "FINAL.json": sha256(final_p),
                      "REPORT.md": sha256(os.path.join(ROOT, "REPORT.md")), "payloads": man["payload_count"]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
