# T027O independent contribution and eligibility review, round 1

Reviewer role: independent CONTRIBUTION/ELIGIBILITY gate for the frozen T027O
author packet `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r36/`.
Written 2026-10-18 (UTC). Only this directory was written. Nothing was
staged or committed, and no shared index was edited. The parallel proof
review, its brief and any proof draft were not read.

Pinned source truths at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are
stipulated. For this gate the unchanged full T027O proof is assumed correct,
as instructed. This is not a proof verdict, acceptance, count change,
publication or claim of worldwide priority. The current count was given no
weight. I am not an author of T027O.

## Verdict

**SUBSTANTIAL (moderate strength, lower half of that band), for the
complete unchanged T027O target in `scope027o.md`.** Not TECHNICAL, not
DUPLICATE, not INELIGIBLE, not BLOCKED.

The verdict carries required credit objections (section 7). They do not
change the classification, but the packet's credit record is incomplete
without them.

## 1. Identity checks, done before parsing

External anchors supplied by the parent were compared with `sha256sum`
before any packet file was parsed. All matched:

| file | SHA256 |
|---|---|
| `manifest.json` | `2127e23fd2698f75585c70ec4be93d599bb449c8d0f20a4bf6013a00cd7f0199` |
| `verify.py` | `2ad360c2d5d89bcd6afe7f875a6097bb55639bc37d62ff258a2582d867c5f5e8` |
| `candidate027o.md` | `e5812790dc336e2184ffbee58882fb154175554b9e23e0cacedeecac6bf48867` |
| `scope027o.md` | `0f53abf319dfde7e8e1e88be77f98a5e0c423dcb0f9ffd99993088dc59b5cda2` |
| `source-and-credit.md` | `e1086b79e6d2d76b290fdd4d8ce9969137fe0f76ee5aea1dfcd01886aade7391` |
| `sources/preprints-tree.json` | `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b` |

The author verifier is read-only. With the correct anchor it returned PASS
(48 files, 8 directories, 13 source blobs); with an all-zero anchor it
failed with `external manifest anchor mismatch`. The 13 author control
cases also behaved as designed on a disposable copy in `/var/tmp` (details
in `author-verification.json`). Independently of the author verifier, I
compared the source family against `preprints-tree.json` (13223 entries,
not truncated): all 13 non-PDF blobs match git-blob SHA-1 and size, with no
extras. The only absent family blob is `paper.pdf`, excluded by design and
therefore not checked. The author packet is tracked and clean in git.

## 2. Target assessed

`scope027o.md`, frozen `2026-10-18T08:13:29Z` before a complete proof or
tangent certificate existed: for every g>=2 and r>=2 there are a number
field L and rho: pi_1(Sigma_g) -> SL_r(O_L) whose Mod(Sigma_g)-orbit of
characters is Zariski dense in the entire complex SL_r character variety
X_{g,r}. No generic-input, marked, torus-normalizer, finite-index or
rank-two replacement is allowed. Rank two is credited to Coccia–Litt. The
candidate theorem in `candidate027o.md` §1 states exactly this target, with
L allowed to depend on r. I saw no narrowing between scope and candidate.

## 3. What the existing operations already pay

**Pinned source027** (`Integral points on character varieties of curves`,
read: introduction, dynamics in full, surfaces lines 1–60 and 180–265,
arithmetic, README). Theorem `thm:main` gives Zariski density of
M_r(X)(O_L) for one fixed L in every rank, so the union of all integral
orbits is already dense. Its closed-surface step pays: the integral model,
irreducibility of the determinant-one relation variety, Dehn-twist torus
saturation of closures, Baire avoidance of countably many resonance loci,
and a submersion argument at one explicit smooth point. That explicit-point
argument only needs the twist motions to vary the spectrum. Density along
the fixed-spectrum fiber comes from the union of integral points, not from
one orbit. The source states no single-orbit result.

**Coccia–Litt** (Prop. 3.1.7 (Whang), Lemma 3.1.8, Prop. 3.1.10,
Prop. 5.0.1, Thm. 5.0.2, read). These pay the whole r=2 case, including
closed surfaces, and the template "one integral point, then a torus action,
then a Zariski-dense orbit". Their mechanism is specific to rank two: the
pants-trace fiber X^P_{k,t} is the image of a torus G_m^{3g-3+n} (Whang),
so twist powers on a perfect fiber fill it, and trace induction finishes.

**Goldman 1986, §§4.2–4.7** (spot-checked). Pays the identification of the
Hamiltonian flow of an invariant function of a simple curve with the
centralizer twist, and the symplectic form.

**Loewy and Mantelos** (Mantelos Thm. 1.1 and the cycle identities read;
Loewy body not read). These pay principal-minor/diagonal-similarity
rigidity. The candidate's infinitesimal principal-minor lemma (§4) is a
direct instance, and the candidate says so.

**Pickrell–Xia I** (§2.1 including Lemma 2.1.16, Defs. 2.1.18,
Prop. 2.1.24, (2.1.29)–(2.1.33), Lemma 2.1.34 with (2.1.35)–(2.1.47); §2.2;
§3 Thm. 3.1 and Lemma 3.10; Appendices A and B through B.5). This is the
closest antecedent for the tangent method. It pays infinitesimal spanning
by centralizer families of twisted products h g^n, the use of dense torus
powers, a BCH/root-space spanning argument, and transverse sewing from
one- and two-holed tori to closed surfaces. It does so for compact K, at
generic boundary data, and in a measure-theoretic (almost-every-point)
framework. It does not certify spanning at any prescribed point, does not
work on the complex closed variety at a degenerate configuration, and makes
no arithmetic selection.

**Golsefidy–Tamam** (new comparator, absent from the author packet; read:
PNAS 2025 text, plus abstract, contents and a rank-term search of the
orbit-closure preprint). Theorem I: for SL_2 and any non-exceptional
sufficiently Zariski-dense point with infinite pure-MCG orbit, the orbit is
Zariski dense in the modified relative character variety. This pays the
rank-two closed case a second time, and far more generally. The PNAS
remark says an SL_d extension via Larsen–Pink "should be possible"; it is
not proved there, and the orbit-closure preprint abstract is SL_2 only.

**Litt survey (arXiv 2409.02234)**. Theorem 5.4.13 gives rank-two Zariski
density of integral points through a single orbit (Shimura-curve local
system with unitary Galois conjugate, plus Previte–Xia [PX02b, Thm. 1.4]).
Questions 5.4.3(2) and 5.4.11 concern density and existence of integral
points, not single orbits. Golsefidy–Tamam state that PX02b Thm. 1.4 is not
correct without excluding exceptional sets.

## 4. Why the naive higher-rank routes do not pay T027O

Three bounded checks show the high-rank single-orbit statement is not a
corollary of the paid material.

1. **No rank-r analogue of the Coccia–Litt torus.** For r>=3 a pants
   decomposition gives (3g-3)(r-1) commuting twist directions, while half
   the dimension of X_{g,r} is (g-1)(r^2-1). Since r+1>3, the pants tori are
   far smaller than a Lagrangian fiber, so twist powers on pants curves
   cannot fill a fiber. A noncommuting family of curves and a full
   cotangent-spanning certificate are needed. This is what T027O supplies.
2. **"Zariski-dense image implies dense orbit" is unavailable in high
   rank.** MathOverflow 332994 records Kapovich's comment that for SU(n),
   n large, Zariski-dense representations with non-Zariski-dense orbits
   exist, and the Biswas–Koberda–Mj–Santharoubane construction of SL(n,C)
   representations with infinite image fixed by the mapping class group. So
   the Litt 5.4.13 route (unitary Galois conjugate plus a dense-orbit
   theorem) has no high-rank input. GLX21 covers only SU(3) on the one-holed
   torus. The specific point therefore matters.
3. **Generic spanning plus source density does not select a point.** Even
   granting a generic spanning open U (plausibly derivable from
   Pickrell–Xia I plus sewing and complexification), one still needs a
   single integral point whose orbit closure meets U at a point where the
   chosen twists are nonresonant. Integral points are countable, so Baire
   cannot avoid countably many resonance loci among them. The source's own
   test point is recorded in the frozen scope as having a monomial-orbit
   obstruction. Some explicit certificate on an explicit orbit-closure
   family is unavoidable.

Two weaker observations: MathOverflow 455985 shows simple-curve
characteristic polynomials do not globally separate points of X_n in
general. T027O needs only local spanning at one point, so this does not
conflict, but it confirms the spanning claim is not a formality. Searches
of Litt's publication list, Golsefidy's research page and the Martin-Baillon
mapping-class dynamics bibliography found no higher-rank single-orbit
integral theorem. This is a bounded search, not a novelty clearance.

## 5. The residual operation and why it is not routine

After the payments above, T027O's new content is one connected operation:

- (a) **Arithmetic seed with a saturating twist** (§§2, 8). A unit polynomial
  of Pisot type gives a cyclic torus generator with only scalar relations.
  The point (I, B, C, I, ..., I) with B = B(m) diagonal integral and
  C = Q C_mu Q^{-1} is integral, and powers of a -> ab sweep A over the whole
  torus T inside one orbit closure. The saturation step itself is the
  source's operation applied to one point; the seed design is new.
- (b) **A full tangent certificate at a degenerate point** (§§3–7). Two
  explicit simple band families u0(k,l), u1(k,l), with based-word
  simplicity checked, give complementary reductions. Vandermonde
  interpolation in k and torus density in l reduce the characteristic
  coefficients to principal-minor data. Two applications of the
  principal-minor lemma and the generic conditions P1, P2 reduce the
  tangent to system (5.1). Its injectivity is proved by a limit argument in
  which h_C consists of complex-symmetric matrices and [H,K] is
  skew-symmetric. Extra handles are handled by (7.1). The certified point
  has A and B in the same torus, so it is not a generic point where
  Pickrell–Xia-type genericity could be invoked.
- (c) **Arithmetic-then-complex selection** (§§8–9). Arithmetic B, Q are
  chosen in a finite intersection of nonempty opens; the complex A that
  meets the tangent open and nonresonance is then found by Baire inside the
  family that already lies in the single orbit closure. This avoids any
  simultaneous arithmetic nonresonance or Hilbert-irreducibility input. The
  flow-invariance argument for a possibly singular component Z0 is a
  careful version of standard material (Goldman flows, Coccia–Litt-type
  torus closure) and earns no separate credit.

Operation-level comparison of (b) with Pickrell–Xia I Lemma 2.1.34: both
use centralizers of products with powers and dense torus powers to reach
infinitesimal spanning. Pickrell–Xia work in a compact group at generic
points of one- or two-holed tori and then sew. T027O must certify spanning
on the complex closed relation variety at one prescribed nongeneric point
lying in a single arithmetic orbit closure. The reduction to (5.1) and the
symmetric/skew injectivity have no counterpart in what I read of
Pickrell–Xia I, the source or Coccia–Litt. I therefore count (a)+(b)+(c)
together as a nonroutine new mechanism, not a transfer.

## 6. Why moderate and not higher

- Every individual tool is paid: saturation, Baire and submersion by the
  source; the single-orbit template by Coccia–Litt in rank two; flows by
  Goldman; the principal-minor lemma by Loewy/Mantelos; the shape of the
  spanning argument by Pickrell–Xia I.
- The conclusion is a strengthening of a source theorem (density of the
  union of integral orbits, already with one fixed field) to one orbit. It
  does not answer Litt's Questions 5.4.3(2) or 5.4.11 beyond what the
  source already gives for curves.
- Experts anticipate a much stronger SL_d statement (the Golsefidy–Tamam
  remark). If that extension were proved, T027O would follow for any
  suitable integral point with infinite orbit. T027O is an explicit,
  unconditional special case of an expected but unproved generalization.
- The novelty evidence is a bounded search, not a literature clearance.

## 7. Required objections (credit; do not change the verdict)

1. `source-and-credit.md` and `candidate027o.md` §10 must cite
   Golsefidy–Tamam (PNAS 122(15) e2416120122, 2025, Theorem I; orbit-closure
   preprint). They also cover the rank-two closed case, and their remark on
   an SL_d extension must be disclosed with the statement that it is not
   proved there.
2. The packet must disclose that T027O is a special case of that anticipated
   generalization, and keep its novelty language at "new to this project;
   bounded search found no higher-rank single-orbit integral theorem".
3. Litt's Theorem 5.4.13 (rank-two single-orbit route via PX02b) should be
   credited as a second rank-two antecedent, with Golsefidy–Tamam's caveat
   on PX02b Theorem 1.4 noted if PX02b is cited.
4. The Kapovich and Biswas–Koberda–Mj–Santharoubane observations should be
   recorded as the reason the high-rank point choice is nontrivial, with
   their source status stated (MathOverflow comment; I did not read the
   BKMS paper body).

Optional improvements: name Pickrell–Xia I Lemma 2.1.34 and
Prop. 2.1.24 next to §6 rather than only in §10; state the dimension count
in section 4 item 1 explicitly as the reason the Coccia–Litt mechanism does
not transfer.

## 8. Eligibility and history

- Family 027 history: I204 screened 027 for a finite-prime Jordan/congruence
  strengthening and refuted that inference with an explicit example; its
  parent disposition parks 027/028 "absent a new mechanism". The r11
  checkpoint says 027 was only catalogue-screened, with no route developed.
  The r23 checkpoint lists "027 (I204)" among history exclusions, which
  refers to the I204 target.
- T027O is a different target (single Mod-orbit density over C, not
  finite-prime Jordan behavior) and supplies a new mechanism. Searches of
  frontier history (including ignored files) found no earlier single-orbit
  or dense-orbit target for family 027. It is new to this project.
- The scope was frozen before the tangent certificate and records the
  unsolved operation at freeze. The candidate states the frozen scope
  without narrowing.
- Eligible. Not INELIGIBLE under the developed-chain exclusion on the
  examined record.

## 9. Disposition of the unchanged scope

If the proof gate passes the unchanged candidate without added hypotheses
or narrowing, this review classifies the full T027O statement as
SUBSTANTIAL (moderate). If the proof gate requires narrowing (for example a
restricted genus or rank range, or a marked or generic-input version), this
verdict does not transfer and a new contribution review is needed. Rank two
alone would be DUPLICATE (Coccia–Litt, Golsefidy–Tamam).

Exact reads and limits are in `reading-limits.md`; history searches in
`history-search.json`; retrieved comparator files in `primary-receipts.json`.
