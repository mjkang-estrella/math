"""One-time seal of this round's own exact selected packet; never grades mathematics."""
from pathlib import Path
import hashlib
import json
import os
import stat

R = Path("frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r235")
assert Path.cwd() == Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
reserved = {"FINAL.md", "MANIFEST.json", "REPORT.md", "ANCHORS.json", "SEAL-CHECK.json"}
assert not any((R / p).exists() for p in reserved)
assert not (R / "SELECTION.json").exists()

def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

paths = sorted(p.relative_to(R).as_posix() for p in R.rglob("*") if p.is_file())
assert not any(p.is_symlink() for p in R.rglob("*"))
paths = sorted(paths + ["SELECTION.json"])
dump(R / "SELECTION.json", {
    "identity": "structural-r235-source359-prefreeze-own-selection",
    "files": paths,
    "reserved_files": sorted(reserved),
    "reserved_subtree": "controls",
    "limits": "Own exact selection only. Envelope REPORT is outside this selection but separately anchored. Controls are freshly bound tiny specimens, never inherited manifests over reduced selections. Protected bodies and metadata stay local under original rights."
})
for p in [R] + [p for p in R.rglob("*") if p.is_dir()]:
    p.chmod(0o700)
for name in paths:
    (R / name).chmod(0o444)
directories = sorted(["."] + [p.relative_to(R).as_posix() for p in R.rglob("*") if p.is_dir()])
manifest = {
    "identity": "structural-r235-source359-prefreeze-own-selection",
    "pin": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
    "seal": "one-time, own selected bytes; no inherited packet",
    "files": [{"path": n, "bytes": (R/n).stat().st_size, "sha256": sha(R/n), "mode": stat.S_IMODE((R/n).stat().st_mode)} for n in paths],
    "directories": [{"path": n, "mode": stat.S_IMODE((R/n).stat().st_mode)} for n in directories],
}
dump(R / "MANIFEST.json", manifest)
(R / "MANIFEST.json").chmod(0o444)
mh = sha(R / "MANIFEST.json")
(R / "FINAL.md").write_text(f"""# Structural r235 — PREFREEZE / no nominee

Authorized Codex / GPT-6 Astra / xhigh / default service tier. Source359 and all operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb were stipulated true. No theorem was frozen; no mathematical grade, acceptance or count is assigned.

The complete retained derivation is in derivations.md. For the source's allowed integer-amplitude threefold it establishes an exact convergent Hilbert feature map, a proper Hilbert-ball embedding, a smooth negative strictly plurisubharmonic exhaustion, completeness of the Carathéodory distance, and uniform comparison of its infinitesimal metric with the paid pinched metric. It also proves the infinite-rank obstruction to exact finite-dimensional complex-hyperbolic isometry and explains why that is not an obstruction to finite bounded embedding.

The eligible original history already supplies the bounded C^5 embedding and is credited unchanged. After the paid source mechanisms, the retained consequences use classical tensor-kernel, diastasis, Schwarz and Cauchy operations. No distinct substantial new operation is claimed. The two-sided Liouville realization and any new finite proper-ball realization remain unproved; the derived isometric obstruction does not settle either.

All 28 canonical blobs were authenticated; all operative TeX/bibliography bodies and figures were read. Precise primary/history extents, late reads, OCR/access limits and accidental editorial exposures are retained in private/reading-limits.md and its referenced records. The pinned Lean declarations use sorry and supply no proved formal coverage.

This exact own selection is sealed once by MANIFEST.json, SHA256 {mh}. REPORT.md is outside the selected packet and separately anchored. Artifact checks do not grade mathematics. No downstream formal/manuscript/release work or public action occurred.
""")
(R / "FINAL.md").chmod(0o444)
fh = sha(R / "FINAL.md")
(R / "REPORT.md").write_text(f"""# Structural discovery r235 — Source359

**PREFREEZE / no nominee.** No exact substantial theorem was frozen. No correctness, contribution, acceptance or count is self-assigned. Campaign 19/20 and latest R041 remain user-provided context; the parent alone integrates and adjudicates.

Authorized provenance: Codex / GPT-6 Astra / xhigh / default service tier. Work stayed within this exact root under the r220 isolation wrapper. The wrapper is not a reused mathematical target. No excluded namespace, peer status or previous closed result was used as a premise.

## Retained mathematics

The integer-amplitude source potential has a convergent Hilbert factor H with ||H||²=exp(phi−psi). The map F(z,w)=(z,wH(z)) satisfies

    1−||F||² = (1−|z|²)(1−exp(phi)|w|²).

The derivation proves properness into the open Hilbert ball, hyperconvexity, complete Carathéodory distance and the global Hermitian tangent estimate

    lambda^(-1) ghat_lambda ≤ gamma_M² ≤ kappa_M² ≤ C ghat_lambda.

Constants belong to one fixed compatible source construction; no unsupported uniform family assertion is made. The proof handles locally normal infinite tensor products, all derivative interchanges it uses, centered charts, and simultaneous base/fiber ends. The paid Kähler metric and its all-real-plane curvature proof remain unchanged. Pointwise bounded-function rank and finite jet interpolation are distinguished from one global bounded local biholomorphism to C^3. Infinite kernel rank excludes exact finite-dimensional ball isometry for ghat_1 only.

See [derivations.md](derivations.md) for the complete calculation and [comparison.md](comparison.md) for the strongest paid/classical reduction. These are research notes, not a downstream manuscript or release.

## What remains unpaid

The complete source mechanisms, classical operations and eligible original C^5 construction leave no identified substantial nominee in this direction. A new two-sided Liouville realization would require a compatible analytic mechanism beyond these constructions: A already has bounded functions separating all points, while B's actual tube formula has no finite lower curvature bound. A new finite proper-ball realization is also unproved; the exact isometric rank obstruction does not rule it out. There is no assertion of impossibility or exhaustive literature novelty.

## Evidence and limitations

All 28 canonical blobs in both specified papers were authenticated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb against the complete tree. All operative drivers/macros/includes, internal estimates and two figure sources were read; both canonical PDFs and READMEs were authenticated only. No catalogue entry or second family was developed. Both source examples and all upstream operative proofs were treated as true.

393 wildcard guards and 162 substring exclusions preceded traversal. Two separately recorded precise history passes preserved the guards; the only mathematical body admitted was the actual overlapping original r25 statement/proof outside the excluded scopes. Its bounded C^5 result is credited unchanged. Coarse omissions and possible opaque false admissions are disclosed, with no exhaustive clearance claim.

Actual primary proofs include bundle/momentum calculations, invariant-metric disk comparisons, disc-bundle curvature operations, Hartogs immersion proofs and the Wermer-set Liouville argument. Primary access and OCR limitations, unread dependencies, late recovery and unintended editorial/header exposures are detailed in [private/reading-limits.md](private/reading-limits.md), with exact byte records. Some analytic antecedents were recovered only as corrupted cached original text; no complete formula-level reading or novelty claim is based on them. All protected bodies and metadata remain private/local under their original rights.

The exact pinned Lean endpoint was read. Its three operative theorem declarations end in sorry; no proved formal support is asserted. No formalization or Lean build was attempted.

## Exact packet and detached anchors

MANIFEST.json binds this round's own explicit SELECTION.json, file bytes and modes. This REPORT is outside that selection and receives its own detached hash in ANCHORS.json. No inherited manifest was attached to a reduced selection. verify_packet.py is read-only and requires the three literal detached anchors. SEAL-CHECK.json records its execution and small newly bound copied controls; those are artifact checks only. Selected bytes are made read-only, and controls do not alter originals.

FINAL.md SHA256: {fh}

MANIFEST.json SHA256: {mh}

REPORT.md SHA256 is detached in ANCHORS.json to avoid self-reference. Parent integration, independent correctness/contribution review and any count remain outside this task.
""")
(R / "REPORT.md").chmod(0o444)
anchors = {"FINAL.md": fh, "MANIFEST.json": mh, "REPORT.md": sha(R / "REPORT.md")}
dump(R / "ANCHORS.json", anchors)
(R / "ANCHORS.json").chmod(0o444)
print(json.dumps({"selected_files": len(paths), "anchors": anchors}, indent=2))
