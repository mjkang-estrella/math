# r245 handback — wide finite/algebraic scout

The counts stay at 9 additional / 39 total / next 40. I claim no credit; only the root accepts. There is no PROOF.md, because the full extremal question remains open. I did no Lean, manuscript, shared, git, browser or MathDB work.

**Breadth.** I screened 22 distinct attributed source questions across ten families:
* sign patterns
* Cayley-graph spectra
* Jacobi–Trudi determinants over F_q
* Latin squares
* tournament matrices
* permutation groups
* words
* numerical semigroups
* quivers
* finite geometry

Every candidate went through a history check and a public-resolution check before any computation. Nineteen are compact rejections or parked rows.

**Strongest new mechanism: refutation of S. Das, LAA 653 (2022), Conjecture 5.1.**
* The source is arXiv:2112.00442v3. The conjecture says minimally AP-irreducible zero-diagonal patterns have at most 2n−2 nonzeros.
* For every n ≥ 4 I give an explicit pattern F_n with 4n−10 nonzeros. The construction is two `+` 2-cycles, a `+`-diamond through n−4 middle vertices, and a mirrored `−` return path.
* So the conjecture fails for every n ≥ 5.
* **Route 1** is a direct proof. Every `+` is unique in its row or column. Each `−` entry is the unique arc leaving the cut U_t: in D(A) for one entry of a mirrored pair, and in D(B_A) for the other.
* **Route 2** is independent machine checking:
  * brute-force verification of F_n for n = 4..30;
  * exhaustive enumeration at n = 4, giving max 6, so the conjecture holds for n ≤ 4;
  * an exact MILP at n = 5, giving max 10 (solver evidence that F_5 is extremal).
* I also proved the upper bound f(n) ≤ 6n−6.
* The source's own Lemma 3.10 is not contradicted.
* **Open:** whether f(n) = 4n−10 in general. The n = 6 MILP failed with a memory error under the fixed caps.
* **Biggest objection:** the result may be judged routine, since random search finds the n = 5 instance in seconds.

**Survivor 2: Abdollahi–Arezoomand–Ebrahimi, arXiv:2305.00279, Conjecture 1.** The conjecture says integral transposition Cayley graphs are exactly those from cographs.
* An exhaustive floating-point screen over all graphs with ≤ 9 vertices found no counterexample.
* The 2-token module almost always witnesses non-integrality. The only exception is K3□K3, which first fails at irrep (6,3).
* No proof mechanism was found.

**Survivor 3: Dwivedi–Blasiak–Grinberg, arXiv:2302.07239, Conjecture 3.3.** All 28 exactly enumerated small cases agree with the conjectured probability. It needs a proof mechanism.

**Access limits.** The LAA journal body is on a denied route (ScienceDirect), so I did not read it. The ISI repository abstract confirms the published paper still proposes the conjectures. I did not read the body of the 2021 IIT Guwahati thesis. Worldwide priority is uncertified.

**Procedural deviations.** A few trivial unguarded `python3` calls are logged in `administrative/deviations.log`. None touched a source.

The final integrity check is `verify.py`, recorded in `receipt.json`.
