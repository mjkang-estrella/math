# No qualifying candidate

Zero new solutions are submitted for acceptance. No Lean endpoint was justified or created. The following exact diagnostic is retained to prevent a later lane from promoting a routine bridge.

## 327907: classical biplane plus a standard union bound — do not count

The source is Goldberg–Rajendraprasad–Mathew, *Domination in designs*, arXiv:1405.3436, Conjecture 8.6 (local primary PDF `sources/http-0009.bin`). It asserts that the incidence graph of every symmetric `(v,k,2)` design with `k >= 4` has domination number `k`.

Take the classical cyclic `(37,9,2)` biplane whose blocks are the translates modulo 37 of

`{1,7,9,10,12,16,26,33,34}`.

The quartic-residue construction is classical. Primary-source corroboration is the biplane discussion in Eugenia O'Reilly-Regueiro's thesis, Section 2.2.3 (local `sources/http-0061.bin` and `.txt`); see also the literature search receipt `receipts/web-007.json`. The script `scripts/biplane.py` independently checks all 666 block pairs and all 666 point pairs have intersection/incidence multiplicity two. It does not rely on a claimed design label.

For any `a >= 1` selected points, their block neighbourhood contains at most `9+7(a-1)=7a+2` blocks: after the first point, every further point has two common incident blocks with the first selected point and therefore contributes at most seven new blocks. Dually, `b >= 1` selected blocks cover at most `7b+2` points.

Suppose nine vertices dominate the incidence graph, with `a` point vertices and `b` block vertices. If either is zero, nine vertices cannot dominate the 37 vertices on their own side. Otherwise `a+b=9`, and domination requires

`37 <= 7a+2+b` and `37 <= 7b+2+a`.

These imply `a >= 5` and `b >= 5`, contradicting `a+b=9`. A dominating set of smaller size could be enlarged to nine, so no dominating set of size at most nine exists. Thus this design has domination number at least ten and contradicts the equality. No claim of an exact domination number above this bound is made.

This is a short standard counting argument applied to an already printed classical construction. It fails the task's substantive novelty standard. It is not submitted as a discovery, and no Lean capacity was spent on it. A bounded web non-finding about this particular observation would not make it novel.

## 359187: stop, exact public Lean target already present

The live Omega repository contains `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.lean`. The exact commit introducing the result is `890d3e89a5c18f28df28fe7defafcd9e25bdea32`, dated 2026-10-02. The current checked HEAD is `de81f09d1b5868b1ef5f62c9c8cab94962481c39`.

The declaration `RectangleRowmotionHomomesy.result` quantifies over all positive rectangle dimensions, every complete reverse linear extension, and every order-convex initial set. Its conclusion is zero sum of max-minus-min over the distinct literal rowmotion orbit. The source computes a corner-count coboundary and telescopes it using orbit permutation. This is the reserved statement, rather than the follow-up's separate signed-cardinality conjecture.

Primary bodies and chronology: `sources/http-0076.bin`, `http-0077.bin`, `http-0078.bin`; corresponding receipts retain URLs and SHA-256 hashes. The public proof body was read; its imported dependencies were not independently rebuilt here. That limitation does not justify rediscovering or crediting the same target.

## Strongest remaining parked route: 328933

Exact carry-graph enumeration agrees with the cyclic Young graph conjecture for every `2 <= n <= 56`, `3 <= t <= 20`. This is 990 completed parameter pairs, with largest completed base 60,761. The intended run to `n=200` hit its CPU cap while working on `n=57`; no completed coverage above 56 is claimed. The first 144-case run is a subset, not additional independent coverage.

The missing lemma is a symbolic classification of all reachable carry pairs and arcs for arbitrary parameters, followed by proof that pivot pruning leaves exactly the required cycle plus the zero node and starting node. Neither finite agreement nor neighbouring printed cyclic constructions provides this lemma. No ordinary proof or formal endpoint has been obtained.
