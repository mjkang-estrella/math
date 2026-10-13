# I216 — reading limits, decisions, and failures

## Scope and early notes

Read AGENTS.md and sources/upstream.json completely. Accepted all pinned theorems and lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The supplied I213 brief/report/analytic/literature record is the starting point, not a new nominated source. The I213 local authentication JSON was read for exact paths and source identities. No active I214 or other live-task output was opened.

A first `rg --files` inventory over source/report filenames was broader than needed and its output was truncated. It exposed filenames, not active report contents. A subsequent catalogue/tree query included the too-generic string `368`, producing irrelevant hash matches and truncation; no mathematical conclusions came from those matches. All substantive source reading was then confined to the two named approximation manuscripts and the existing named primary copies. This is recorded rather than presented as an exhaustive corpus search.

Partial report, analytic note, reading log and literature note were written before the decisive source operation was located. The early note said no theorem had yet been proved. A second partial analytic entry recorded the inverted-collar mechanism before final checks. The final analytic note supersedes that tentative status.

## Pinned readings

- High-range introduction: all 251 lines, with overlaps to recover text from a truncated combined tool response. Actual main theorem, limitations, conventions and local tolerance lemma read.
- High-range smoothing: all 1019 lines, in overlapping chunks 1–250, 251–550, 550–850, 850–end. The complete bilipschitz-to-PL and PL-to-smooth arguments were read before asserting relative exterior preservation. This extends I213's limited smoothing read.
- High-range preparation: label/keyword location followed by the exact windows recorded in the JSON. In particular `hp:smooth-cutoff` statement and proof, lines 1945–2046, were read completely, along with the original cutoff hypotheses. `hp:carrier` and `hp:full-rank-correction` confirm overlap. No full-paper reading is claimed.
- High-range assembly: lines 1130–1258, including the complete concluding main-theorem proof. This calls smooth cubical corrections before a final smoothing.
- Low-range introduction: lines 1–85, including the main theorem and boundary limitations. This is a companion-contract check, not use of low-range proof results.
- Bibliography: only the entries for Campbell–D'Onofrio–Vítek, Hamilton, Edwards–Kirby, Smale, Hatcher and Li–Watts located with context.
- Catalogue: family 368 entry with nearby lines; complete tree parsed for exact two-family paths and blob comparison, not semantically read as a corpus.

## Mechanism A: ambient isotopy/localized velocity

A flow of χv preserves injectivity, unlike scalar interpolation of endpoint maps. The derivative ODE gives the explicit sufficient estimate C exp((1+3/p)L)Q, with L the integrated L∞ derivative and Q the integrated W^{1,p} velocity on the swept annular region. This was not converted into an unconditional endpoint estimate. Compact-open topology and qualitative isotopy extension do not bound L or Q. A fixed smooth input admits many choices with finite constants, but those constants are not uniform along rough approximating sequences. No claim that this failure refutes the target was made.

## Mechanism B: smooth cubical cutoff and relative smoothing

The decisive change was locating the already paid `hp:smooth-cutoff`, which takes the smooth approximants themselves as input. This avoids the uncontrolled energy of the general topological opening. A fixed smooth radial inversion maps a cube boundary into the desired arbitrarily thin annulus; the interior smooth filling is discarded by the cutoff and does not enter its energy bound.

Checks made analytically:

1. The approximate cube radial profile is fixed before j and gives strict inner/outer radii.
2. A round sphere inside the cube maps to a compact region of 2B outside the rough support; its smooth image can be filled with the prescribed collar.
3. The dyadic cutoff width is chosen at least a fixed multiple of uniform displacement, satisfying the actual input condition.
4. Conjugated shell derivatives are controlled on fixed annuli, including at the image points of K.
5. K's image shell avoids zero since K fixes Q. Hence the inverse chart introduces no singular factor there.
6. H uses G near physical zero; inversion is never evaluated at zero.
7. Interface agreement is on neighborhoods where needed; the remaining inner seam is locally bi-Lipschitz by the source lemma.
8. Proper local homeomorphism plus identity near infinity gives global bijectivity.
9. Strong relative smoothing is justified from source local operations with a fixed exterior buffer, not from a bare PL approximation statement.
10. Exact agreement with G on the inner ball is only claimed before that smoothing. The closed-ball density theorem needs only the exterior identity afterwards.

The source already applies the same smooth cutoff for full-rank corrections. Thus the final theorem is classified **technical source overlap**, even though it resolves the target left unresolved in I213. No count change is proposed.

## Stronger target after the overlap check

Attempted LD_p: a uniform linear W^{1,p} correction cost with exact smooth inner and outer agreement, independent of inverse distortion and higher derivatives. The available estimate gives a pth-error O(η+d^p), and Morrey gives η=O(d), hence only O(d^{1/p}). The required s≳η prevents eliminating the baseline shell-volume term by choosing an arbitrarily thinner shell. The positive squeeze parameter controls the hole error but does not remove that term. This is a precise unpaid estimate, not a counterexample or a nomination.

The supplied fixed-cutoff fold remains a counterexample to the naive argument. It was neither ignored nor counted as new. No compression proof or old technical partial was repackaged as a contribution.

## Primary literature checks and limits

Existing IKO extraction lines 1–130 were read for the exact relative planar theorem. Existing Hencl extraction lines 1–220 were read for context; no full reread is claimed. The Campbell–D'Onofrio–Vítek v2 introduction/main statements were inspected online, not copied or read in full. Edwards–Kirby PDF introduction, definitions, Theorem 5.1 statement and associated returned excerpts were inspected online, not its complete proof. Li–Watts was bibliographic/title-page verification only. The external Hatcher PDF open returned `Internal Error`; the source's accepted filling operation is the proof dependency.

Three bounded search queries in the final batch and two in the initial batch were for primary prior art. No secondary hit, live-task page, or search-result absence was used as a theorem. No worldwide novelty or current-open-status assertion is made for LD_p.

Only assigned I216 paths were written. No subordinate agents, research code, numerical/parameter scans, tests, snapshots, seals, historical replay, shared/ancestor edits, staging, commits or publication. Text editing and provenance hashing scripts did not perform mathematical experiments. No new source copies were created; existing copies were read in place. Detached output/source hashes are separate from proof and contribution acceptance.
