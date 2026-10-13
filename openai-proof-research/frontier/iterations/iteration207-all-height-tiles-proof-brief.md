# I207: independent proof review of I203 all-height covering nomination

Work only in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md and sources/upstream.json. All theorems and lower operations
at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.
Eight substantial findings accepted, two remaining. Use the user's
GPT-6.1 Sol/high/ultrafast settings. No subordinate agents.

The complete original I203 brief, returned report, full analytic record,
source-boundary note and parent response accompany the prompt. This is an
independent PROOF gate. Contribution is a separate gate and is not settled
by a proof PASS. The author nominates a result; the parent has not accepted it.

Review Theorem 1: for every trace-zero elliptic real 2-by-2 matrix A and
L>0, the infimum of |F|/covol(Gamma) over bounded measurable F and full-rank
Gamma with F+(I+sA)Gamma=R^2 at every |s|<=L equals 1+L^2 det A, attained
by the displayed compact parallelogram. Also review Theorem 3's finite
nonlinear cylinder cover with multiplier 1+L^2(det DV)_+ and its claimed
stability. Clearly separate any valid narrower theorem from an overclaim.

Do your own derivation. In particular attack:

- B,G determinants, the path identity, endpoint and irrational-height
  coverage, and the exact hypotheses of the accepted square-grid lemma.
- The second staircase proof when b<0, existence of the least crossing,
  boundary conventions and its change of lattice basis.
- Transfer to every nonnormal elliptic A, normalization of area/covolume,
  and the lower bound over the entire declared admissible class.
- Uniform templates above a determinant cutoff, fallback below it,
  inverse estimates, finite retention, actual coverage before integration,
  arbitrary compact/positive-area boundary sets, order of cutoff and mesh
  choices, and physical perpendicular-base area.
- Any overstatement in auxiliary Fourier/fractional/regularization claims
  that affects the nominated theorem. Identify separable nonessential
  errors rather than silently changing the theorem.

Source truths are accepted: check whether their hypotheses apply, not
their upstream validity. No research code, numerical scans, automated
tests, snapshots, seals or old replay. Written algebra and geometric
checks, source retrieval, text search and hashing are allowed.

Return PASS, FAIL, or PASS WITH EXPLICIT REPAIRS, with an exact final
theorem scope, independent reasoning, objections and source contracts.
Do not edit the author's files. A complete counterexample or proof gap
must be recorded even if the result appears promising. Do not assess a
short proof as novel merely because it is correct.

Only write `frontier/reviews/i207-all-height-tiles-proof.md`,
`frontier/experiments/i207_all_height_tiles_proof/input-authentication.json`,
and `frontier/sources/i207_all_height_tiles_proof/literature.md` plus fully
read, hash-recorded source copies there. Read existing inputs in place
where possible; no recursive archive audit. Write partial review notes
early. No shared/ancestor edits, staging, commits or publication. Other
live-task outputs and I31 are outside scope. Return detached output hashes.
