# MathDB 324342: refutation of the conference-matrix MDS conjecture (r4 dossier)

Status: **candidate, 0 credit.** Independent fidelity review, novelty/significance review, paper and root acceptance are all still pending.

## 1. Source statement and definitions (primary bodies read)

**MathDB literal** (corpus chunk 0002, line 3870; line sha256 `73a0bb42…1342`):

> Let p be a prime, and let C be a code of length p+1 constructed from a generator matrix that is a conference matrix. The code C is an MDS code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2.

The source is Etzion, Vardy and Yaakobi, *Coding for the Lee and Manhattan metrics with weighing matrices*. Four versions were compared. All four keep the conjecture verbatim and unresolved.

| Version | Where read | Statement |
|---|---|---|
| arXiv v1 (21 Oct 2012) | `fresh-corpus-r3/sources/1210.5725v1.txt` | Conjecture 5 |
| arXiv v2 (11 Dec 2012) | `fresh-corpus-r3/sources/1210.5725.txt`, lines 285–304 and 1129 | Conjecture 5 |
| ISIT 2013 | `fresh-corpus-r3/sources/web/28_Lee_Manhattan_ISIT13.txt`, lines 165–182 | Conjecture 1 |
| IEEE TIT 59(10):6712–6723, Oct 2013, author-posted copy | `web-untrusted/r4/IT13.pdf` (see below) | Conjecture 1 |

Details of the TIT copy:
- URL: `yaakobi.net.technion.ac.il/files/2015/04/7_Lee_Manhattan_IT13.pdf`, sha256 `a7b49ca6…c9f9`.
- The PDF's xref is damaged. Only Flate text streams were recovered, by `scripts/pdf_stream_scan.py`, and the math glyphs are missing from them.
- What it does show: the conference-matrix definition; Theorem 4; the sentence "We have examined the code reduced from Λ(W) over the alphabet Z_p for the minimum distance in the Lee metric … We believe that a surprising result will be derived if we will examine the Hamming distance of these codes"; Conjecture 1, "…is a maximum distance separable (MDS) code of dimension … and minimum Hamming distance …"; the same Paley-only verification remark; and open problem 2 in the conclusion.
- The "2015" in the URL is only the upload date. The journal version is 2013.

Source definitions (§I) and how the Lean file encodes them:

- **Weighing matrix W_{n,w}.** An n×n matrix over {0, 1, −1} with exactly w nonzero entries in every row and every column, and W Wᵀ = w Iₙ. In Lean: `IsWeighingMatrix`.
- **Conference matrix.** A weighing matrix with w = n − 1. In Lean: `IsConferenceMatrix`.
  - The source does *not* require a zero diagonal or skew-symmetry.
  - The textbook definition (zero diagonal, ±1 off the diagonal, CCᵀ = (n−1)I) is also formalised, as `IsStdConferenceMatrix`, and refuted too.
- **The code.**
  - The §II/Theorem 1 construction is the code over Z_w reduced from the lattice Λ(W), the integer span of the rows.
  - Here w = p, so the code is the reduction mod p of Λ(W). In Lean this is `latticeCode`.
  - That equals the F_p row span `rowCode`; the Lean lemma `latticeCode_eq_rowCode` proves this for every p, n and W.
  - Theorem 4 says its rank over Z_p = F_p is (p+1)/2, which fixes the code as this row space.
- **Hamming minimum distance.** The least Hamming distance between distinct codewords (`minDistance`). The variant "least nonzero weight" is `minWeight`; both are refuted.
- **MDS.** Singleton equality d = n − k + 1, with k = `Module.finrank` (`IsMDS`).
- **Quantifiers.** For every prime p and every conference matrix W of order p+1, all three clauses hold. The authors verified it only for Paley matrices up to n = 23, and that check is their evidence, not a hypothesis of the conjecture. No family or case is excluded by the source.

## 2. Ordinary proof of the refutation (p = 19, n = 20)

**Construction.** Take ±1 sequences of length 5:

| Sequence | Values |
|---|---|
| a | (1, 1, 1, −1, −1) |
| b | (1, 1, 1, 1, −1) |
| c | (1, 1, 1, 1, −1) |
| d | (1, 1, −1, 1, −1) |

- a is skew-type: a₀ = 1 and a₅₋ᵢ = −aᵢ.
- Their periodic autocorrelations sum to 0 at every shift t = 1, …, 4.

Let A, B, C, D be the corresponding circulants and R the back-identity. The Goethals–Seidel array then gives a skew-Hadamard matrix H of order 20: HHᵀ = 20I and H + Hᵀ = 2I.

Put W = H − I. Then:
- W has zero diagonal and ±1 entries off the diagonal.
- Wᵀ = I − H = −W.
- WWᵀ = HHᵀ − H − Hᵀ + I = 19I.

So every row and every column has exactly 19 nonzeros, and W is a conference matrix in the source's sense and in the textbook sense. All of these facts are also checked directly on the explicit 20×20 integer matrix, by `scripts/gs_reconstruct.py` and `scripts/verify_from_scratch.py`, and in Lean by `W20_conference`, `W20_std_conference` and `W20_skew`.

**Dimension.** Let C ⊂ F₁₉²⁰ be the row span of W mod 19.
- The 10×10 block of rows 0–9 and columns 0–9 has an explicit inverse B. So rows 0–9 are independent.
- Each row r is an explicit combination Σₜ D_{r,t} · row_t of rows 0–9.
- Hence dim C = 10 = (p+1)/2, in agreement with the source's Theorem 4.

**A weight-9 codeword.** With coefficients x = (5, 7, 13, 9, 0, 15, 14, 2, 8, 18, 0, …, 0) we have Σᵢ xᵢ · rowᵢ ≡ c (mod 19), where

c = (0,0,0,0,0,15,0,0,10,1,18,0,9,0,18,14,5,15,0,0).

c has support {5, 8, 9, 10, 12, 14, 15, 16, 17}, so its Hamming weight is 9. Therefore d(C) ≤ 9.

**Conclusion.** For a [20, 10] code the Singleton value is n − k + 1 = 11 = (p+3)/2. Since d(C) ≤ 9 < 11:
- C is not MDS;
- d(C) ≠ (p+3)/2.

The literal universal statement fails at p = 19. Only the dimension clause, which is the source's Theorem 4, holds. ∎

**Exact distance (computer, not Lean).** d(C) = 9 exactly. Method (`scripts/verify_from_scratch.py`): every nonzero word of weight ≤ 10 vanishes on some 10-set S of coordinates, so enumerating all C(20,10) = 184,756 sets S, with the kernel of the RREF basis restricted to each, finds every such word.

| Quantity | Value |
|---|---|
| Dependent 10-sets | 8,160 |
| Kernel dimension at each | exactly 1 |
| Projective words of weight 9 | 180 (3,240 nonzero codewords) |
| Projective words of weight 10 | 6,180 |
| Consistency check | 11·180 + 6,180 = 8,160 |

The counts come from `scripts/low_weight_count.py`. So C is a self-dual [20, 10, 9] code over F₁₉, where self-duality follows from WWᵀ ≡ 0 and dimension n/2.

## 3. Contrast with the Paley case (context only; not claimed, routine)

Let p be an odd prime and W the bordered Paley conference matrix, with entries W_{i+1, j+1} = χ(j − i). By Euler's criterion, χ(j − i) ≡ (j − i)^{(p−1)/2} mod p, which is a polynomial in j of degree k − 1, where k = (p+1)/2, with leading coefficient 1.

So, up to sign-scaling column 0 (ε = ±1):
- row i+1 is the doubly extended Reed–Solomon codeword of (x − i)^{k−1};
- row 0 is that of the constant 1, whose coefficient at infinity is 0.

The Paley code therefore lies inside the doubly extended RS [p+1, k, p+2−k] code. Dimensions agree, so the two codes are equal and the Paley code is MDS for every p.

Consequences:
- The Paley-only reading of the conjecture is true and easy.
- The source's checks up to n = 23 are consistent with this. Re-verified here by exhaustive k-column rank for p ≤ 19 (`logs/paley_control.log`).
- Monomially equivalent conference matrices give codes with the same minimum distance. Since C has d = 9, W is not equivalent to the order-20 Paley matrix. That Paley matrix is MDS, which was rechecked.
- I make no claim that 20 is the smallest counterexample order. That would need a classification of all conference matrices of orders 4, 6, 8, 12, 14 and 18, which I did not audit.

## 4. Lean endpoint (`lean/ConferenceMDS324342.lean`)

The file is generated from `data/lean_cert.json` by `scripts/gen_lean.py` and `scripts/Template.lean`.

Main theorems:
- `conjecture5_false : ¬ Conjecture5`. This is the literal universal statement, with the source definition of conference matrix, the row code, `minDistance` built on `hammingDist`, `IsMDS` as Singleton equality, and `finrank`.
- `conjecture5Std_false`: the same, with the textbook definition.
- `mds_claim_false` and `distance_claim_false`: each clause refuted on its own.
- `conjecture5_minWeight_false`: the minimum-weight variant.
- `counterexample`: packages together
  - primality of 19;
  - both conference properties and skewness;
  - `latticeCode = rowCode`;
  - finrank = (19+1)/2;
  - minDistance ≤ 9 and minWeight ≤ 9;
  - minDistance < (19+3)/2;
  - ¬IsMDS.
- `latticeCode_eq_rowCode`: a generic bridge proved with `Submodule.map_span` and `Submodule.restrictScalars_span`.

**Non-vacuity control** (`audit/Controls.lean`). Under the same definitions, the Paley matrix of order 4 satisfies *all* clauses: `paley3_satisfies` proves it is a conference matrix, is MDS, has finrank 2 and has minDistance 3. This shows the definitions are not trivially falsifiable.

**Replay** (`replays/final/`). `scripts/replay.sh` copied the packet into a fresh empty directory, regenerated the certificates and the Lean file from the frozen matrix alone, and got a file byte-identical to the packet. It then ran:

| Check | Wall time | RSS | Result |
|---|---|---|---|
| Forbidden-token scan (sorry, admit, axiom, unsafe, native_decide, ofReduceBool, implemented_by, extern, opaque, partial, set_option, …) | — | — | empty |
| `lean -DwarningAsError=true -o …olean` | 10.0 s | 7.3 GB | rc 0, no output |
| `Audit.lean`: `collectAxioms` on every declaration of the module | — | — | 90 declarations, 0 outside {propext, Classical.choice, Quot.sound} |
| `leanchecker ConferenceMDS324342` (non-fresh) | 9.3 s | — | rc 0 |
| `Controls.lean` | — | — | rc 0, axioms {propext, Classical.choice, Quot.sound} |

Finite facts are proved by `decide +kernel` only.

Resource limits: systemd scope with MemoryMax 12 GB and CPUQuota 200%, plus `taskset -c 0,1` and a 1,500 s timeout per call.

Pins are in `provenance/pins.json`: Lean 4.34.1 (commit 5045d005), mathlib d13f23b7 and the package revisions. The prebuilt oleans at the pinned revisions are trusted as-is, and leanchecker did not re-check Mathlib.

Earlier attempts are kept as diagnostics:
- `replays/r1`: the Audit elaborator had a typing error.
- `replays/r2`: leanchecker could not find `lean` on PATH.
- `lean/compile1.log`: an ambiguous `smul_apply`.

## 5. Relation to the old r3 lane's artifacts (automatic resumption, 08:00–08:21 UTC)

Timeline:
- After its rate-limit reset, the old r3 worker resumed automatically. Root confirms this.
- While r4 was working, it rewrote `conference/gen_lean.py` and `sources/receipts.json`. Those are the two input-binding mismatches in `provenance/input-bindings-after.json`; the other 40 bindings match.
- It also created `conference/lean/*`, `PROOF.md`, `SUMMARY.md`, `results.json`, and other files.
- r4 read r3 files only, and none of r4's results depend on the two changed files.
- So the mismatches are caused by that worker, not by corruption. Snapshots: `provenance/r3-snapshot-*.txt` and `provenance/r3-sha256-at-start.txt`.

Comparing r3's final `ConferenceMDSCounterexample.lean` (sha256 `1b355df8…df21`) with this packet:
- **Same core semantics.** `IsWeighingMatrix`, `IsConferenceMatrix`, `rowCode`, `minDistance`, `IsMDS` and `Conjecture5` are textually equivalent in the two files.
- **Same embedded data.** The matrix rows, the inverse B and the row expressions D are identical. Both lanes derive from the same frozen witness and make the same deterministic choice of rows and columns 0–9, so this is a replication of one certificate, *not* an independent second witness.
- **What r4 adds:**
  - the lattice-reduction bridge, which matches the TIT phrase "code reduced from Λ(W)";
  - the textbook-definition and minimum-weight variants;
  - per-clause refutations;
  - the Paley p = 3 non-vacuity control;
  - an axiom audit of all 90 module declarations;
  - a replay that regenerates the Lean file byte-identically from the matrix;
  - a partial read of the author-posted TIT body.
- **Corrections to r3:**
  - r3 refers to an unread "2015 IEEE TIT version". The journal version is TIT 2013, and a partial author-posted body was read here.
  - r3's "2,767 order-20 GS matrices all non-MDS" figure is not verified by r4 and is not claimed.

## 6. Prior-art and registry checks (bounded)

**Versions.** All four keep the conjecture open (§1).

**Citing works.** OpenAlex lists 13 works citing the TIT paper, 3 citing the ISIT paper and 0 citing the arXiv record (`web-untrusted/r2/*.cites`). None of the titles concerns conference-matrix codes or MDS codes. **I screened these by title only; their bodies are unread.**

**Web searches** (standard and extended):
- No counterexample or resolution was found.
- Nearest work: Arasu–Gulliver, *Self-dual codes over F_p and weighing matrices*, IEEE TIT 47 (2001). Its abstract mentions conference matrices and examples up to length 40, which suggests [I | W]-type codes of length 2n rather than the length-n row span. **Body unread (paywalled).** This is a residual subsumption risk for the reviewer.
- Grassl–Gulliver, ISIT 2008: the source cites it for constructing self-dual MDS codes. Body unread.
- Li–Zhou, arXiv:2512.19312: Paley graphs and GRS self-dual MDS codes. Body read; no conference-matrix code content.

**MathDB.** Page fetched once by r3 at 04:46 UTC: HTTP 200, 0 solutions, 0 model attempts, 0 formulations. The later inherited MathDB 403 was not retried.

**openai/math.**
- Head refreshed at 08:11:01 UTC: still `4eaee87548250b2682affda7d05d947c05554bae`, the same as r16 observed at 07:40:39 UTC.
- `CONTENTS.md`, `history.md` and `README.md` were fetched at that head. None mentions conference, MDS, Etzion, weighing, Manhattan or 324342.
- Path screens:
  - root tree reused from r3 at the same head: truncated, 0 hits;
  - complete preprints subtree reused from r10 (`3f56f68a…`): only unrelated Hadamard titles.
- These are path screens only, not a full-body clearance.

**Palomar.** The r3 receipts at 04:46 show revision 651 returning an empty list for every query. The inherited 403 was respected and nothing was retried.

**Accepted families.** None of the 40 accepted results (31–39, the first-campaign list and 388087) is in coding theory or about MDS or conference matrices.

**Missing-body limits:**
- the TIT math glyphs (damaged PDF);
- the bodies of Arasu–Gulliver 2001 and Grassl–Gulliver 2008;
- citing-work bodies;
- current MathDB comment and solution state after 04:46 UTC.

**Novelty** is therefore bounded and not certified worldwide.

## 7. Significance (for the independent reviewer; not self-assessed as passing)

For:
- It refutes, in exact scope, a conjecture that has been explicitly open in a peer-reviewed IEEE TIT paper since 2012–2013. The authors also list it as open problem 2.
- The counterexample is small and fully explicit: a skew conference matrix of order 20 whose code is [20, 10, 9].
- It sharpens a clean dichotomy. Paley matrices always give doubly extended RS (MDS) codes, but a non-Paley Goethals–Seidel matrix of the same order does not.

Against:
- It is a single computer-found counterexample to a side conjecture in a Lee-metric paper.
- The Paley contrast is routine.
- The authors' own wording ("surprising result") suggests the expectation was weak.
- A domain expert may regard non-MDS-ness for non-Paley matrices as unsurprising. By Ball's 2012 theorem on MDS codes over prime fields (cited from memory, body not read, not used in any proof), an MDS code of this length would have to be GRS, which is a strong rigidity requirement.

Root and independent reviewers should decide whether this meets the "mathematically significant" bar.
