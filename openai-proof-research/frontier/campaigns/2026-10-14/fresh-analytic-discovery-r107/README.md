# r107 research handoff

Status: **AUTHOR_FULL_PROOF; INDEPENDENT_PROOF_AND_CONTRIBUTION_GATES_PENDING**.
No nomination or acceptance credit is entered. Campaign count remains 18/20
as supplied by the parent. This packet does not certify substantiality.

The frozen T333E107 target is the existence of a smooth isometric embedding
into exactly R4 for every closed smooth orientable surface with every smooth
positive definite metric. `proof.md` gives a complete author deduction from
the stipulated source333 operations without narrowing that scope.

The added argument projects along the source velocity plane, which is
transverse to the old tangent plane by its phase-Hessian inequality. It
annihilates the entire oscillatory derivative, making the projected exact map
C1-close to the old embedding. Injectivity then survives every finite source
step. Ordinary orthogonal normal projection is insufficient; the explicit
two-jet in `hostile-checks.md` shows why.

The substantive-contribution issue is unresolved. The source pays all analytic
correction and finite assembly, and primary literature already treats embedding
preservation under corrugation as standard. `operation-comparison.md` puts that
objection alongside the exact added mechanism. An independent reviewer may
reasonably conclude this is a technical or source-companion consequence; an
author proof is not a contribution PASS. No mathematical gap is currently
identified by the author, but there has been no independent proof gate either.

Read `scope-freeze.md`, `proof.md`, `operation-comparison.md`, `hostile-checks.md`
and `reading-limits.md`. The two provenance JSON files record exact acquisition
identities. `manifest.json` binds every retained payload and selected external
anchors. `verify.py` reads only and requires the externally supplied manifest
digest. Run from this directory:

    python verify.py --expected-manifest <DETACHED_SHA256> --repo-root /home/mj-kang/Documents/Dev/math/openai-proof-research

The verifier's success is an integrity result only. `seal.sha256` is a convenience
copy; use the detached digest supplied in the final handoff. Private evidence
is excluded from any original-prose publication claim. All work stays local;
no publication, shared-index change, staging, commit or nested agent was used.

`integrity-controls.json` records two intact-bundle checks and seven rejection
controls: wrong external digest, modified proof, extra or missing payload,
symlink substitution, external-anchor drift, and modified manifest. They used
an earlier manifest before this receipt and final editorial changes were added.
The final manifest was separately verified after resealing; no test result is
presented as mathematical proof.
