#!/usr/bin/env python3
"""Seal the review once: write packet/MANIFEST.json, outside REPORT.md, FINAL.json and their .sha256 files."""
import hashlib, json, os, sys
from pathlib import Path

VERDICT = "TECHNICAL"


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    root = Path(sys.argv[1])
    pk = root / "packet"
    for p in (pk / "MANIFEST.json", root / "REPORT.md", root / "FINAL.json"):
        if p.exists():
            raise SystemExit(f"already sealed: {p}")
    files = []
    for dp, dn, fn in os.walk(pk):
        for f in sorted(fn):
            p = Path(dp) / f
            files.append({"path": p.relative_to(pk).as_posix(), "size": p.stat().st_size, "sha256": sha256(p)})
    files.sort(key=lambda e: e["path"])
    (pk / "MANIFEST.json").write_text(json.dumps({"version": 1, "files": files}, indent=1) + "\n")
    man = sha256(pk / "MANIFEST.json")
    review = sha256(pk / "public/review.md")
    limits = sha256(pk / "public/reading-limits.md")
    report = f"""# REPORT T184I134 contribution review round 1 (outside packet)

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Independent substantial-contribution review only.
No correctness gate, acceptance, count, priority or parent verdict. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true.

Verdict (conditional on correctness, entire unchanged frozen scope): {VERDICT}.

Author (immutable, authenticated read-only): FINAL 27ee1a396bda9f1bf61a24177cf8a8e753033c5e73234c78071a74fa928bbdf9,
MANIFEST 4264a6d43c8848418f01353f0cf3b8bb144b8dcc3943251712e8782cf6d967b0, REPORT 60c0a4806dd4135466d1b4cb553039ef01cac230db775424fc0bd9f72aab5b2f,
scope 4d491e34d80254c3b6b0d4d7a289500505bb2826fc4e4db4b3de55a92913221c, proof 0ec0b117efaeba1e692265d7f62810dedaf5010bc47f5b640bad066f63ea46e2.

Strongest reduction: Kang, Zenodo 23351325 v1 (13 Oct 2026), Lemma 2.2 (triangle control at entropy-minus-edge maximisers
implies log Z_G(lambda) >= Psi*_(G,rho)/C, same averaging, same recurrence i(G)=i(G-v)+i(G-N[v]), same closing inequality),
applied at C = max(4, 2B_r), lambda = 1/(C-1), rho = 1, with source eq:optimizer-triangle, gives log i(G) >= F*_G/max(4,2B_r)
>= F*_G/(3C_r) (part 1). Kang Theorem D states the K_r-free mean-field bound (r >= 4). Part 2 is the standard test weight
(source prop:maximum-degree computation after Davies' (3.4)->(3.5) separation); part 3 is Jensen (and Kang (18) / CDM).
Without Kang: source eq:averaged-deletion-cost used termwise (no Jensen) plus Davies Section 3 averaged-pivot recurrence.
Davies Section 3.3 / proof of Theorem 17 read in full: max-weight pivot, boosted weights, pointwise mad control of
neighbourhood edges; does not transfer verbatim to r >= 4, and the needed replacements are already paid.
Remaining: no nonroutine operation; part 2's display not found verbatim (one-step corollary). Not REDISCOVERED as a whole.

Review: packet/public/review.md SHA-256 {review}
Reading limits: packet/public/reading-limits.md SHA-256 {limits}
Packet MANIFEST SHA-256: {man}
Verifier: python3 -B packet/public/verify.py --root <this root> --project <openai-proof-research> --final <FINAL.sha256> --manifest <MANIFEST sha> --report <REPORT sha>
Disclosed isolation slip: /tmp/x (history path list) written and deleted during the review.
"""
    (root / "REPORT.md").write_text(report)
    rep = sha256(root / "REPORT.md")
    final = {
        "version": 1, "status": "SEALED_CONTRIBUTION_REVIEW", "review_label": "T184I134 contribution r1",
        "verdict": VERDICT, "conditional_on_correctness": True, "correctness_gate_assigned": False,
        "count_assigned": False, "provider": "Factory Droid", "model": "claude-opus-5-5",
        "pin": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "author_final_sha256": "27ee1a396bda9f1bf61a24177cf8a8e753033c5e73234c78071a74fa928bbdf9",
        "manifest_sha256": man, "report_sha256": rep, "review_sha256": review, "reading_limits_sha256": limits,
    }
    (root / "FINAL.json").write_text(json.dumps(final, indent=1) + "\n")
    fin = sha256(root / "FINAL.json")
    (root / "FINAL.sha256").write_text(f"{fin}  FINAL.json\n")
    (root / "REPORT.sha256").write_text(f"{rep}  REPORT.md\n")
    print(f"FINAL {fin}\nMANIFEST {man}\nREPORT {rep}\nREVIEW {review}\nLIMITS {limits}")


if __name__ == "__main__":
    main()
