# Candidate: a counterexample to MathDB 377831

Status: candidate for independent fidelity, significance and novelty review; zero credit pending root acceptance. This is not a publication or a worldwide priority claim.

## Exact source

L. Yu. Glebsky and Carlos J. Rubio, *Latin Squares, Partial Latin Squares and its Generalized Quotients*, arXiv:math/0303356v1 (27 March 2003), Definition 2 and Theorem 2, PDF pp. 3–4; Definition 3 and Conjecture 2, PDF pp. 5–6. The downloaded PDF, extracted text and dated hash receipt are in `sources/math_0303356.*`. The literal MathDB record and exact original JSONL line are bound in `extracted.json` and `raw/377831.jsonl`.

The source has S a subset of (k)^2. The MathDB paraphrase loses the exponent. Lines fix two coordinates and vary the third; they are not coordinate planes. An S-partial quasigroup operation is defined at every pair in S and has no repeated output in a row or column. A generalized quotient uses an arbitrary partition into k nonempty classes, not necessarily equal classes. The conjecture asserts that rho(H intersect (S times (k)))=|S| implies that H contains such a quotient. The counterexample uses S=(3)^2, so on the underlying finite set the required partial operation is everywhere defined. It is therefore an actual quasigroup. This full-S specialization handles every possible nonuniform partition and does not refute merely the uniform version.

## Counterexample and covering certificate

Use indices 0,1,2 (add one for the paper's convention). Let H have these allowed third coordinates in each row/column cell:

| first coordinate | second 0 | second 1 | second 2 |
|---|---|---|---|
| 0 | {2} | {0,1} | {0,1,2} |
| 1 | {0,1} | {1,2} | {0,2} |
| 2 | {0,1} | {2} | {1,2} |

There are 17 triples. Give weight 2 to (0,0,2), weight 0 to (0,2,2), and weight 1 to every other triple. The total weight is 17. Each of the 27 possible coordinate lines has weight at most 2 (the 27 finite checks are proved by kernel `decide` in Lean). Any cover by m lines consequently satisfies 17<=2m, so m>=9. The nine vertical lines cover H. Hence rho(H)=9=|S|.

## No nonuniform quotient is possible

Define three integer matrices, with rows and columns ordered 0,1,2:

    A = [ 0  0  1 ]     B = [ 1  0  0 ]     C = [-1  0  0 ]
        [-1  0  1 ]         [ 0  0 -1 ]         [ 0  0  1 ]
        [-1  0  0 ]         [ 0  0  0 ]         [ 0 -1  0 ].

Every (i,j,z) in H satisfies A[j,z]+B[i,z]+C[i,j]=0. These 17 equalities are again kernel-decided, not assumed.

Suppose a finite quasigroup Q, with operation *, has a surjective class map pi:Q->{0,1,2} and quotient support contained in H. Let r_i be the positive size of class i. Sum the displayed score equality over every (a,b) in Q^2. Each row and column of a finite quasigroup is a permutation. Thus the three resulting sums are respectively

    sum_{j,z} r_j r_z A[j,z],
    sum_{i,z} r_i r_z B[i,z],
    sum_{i,j} r_i r_j C[i,j].

Their total is sum_{i,j} r_i r_j T[i,j], where

    T=A+B+C = [ 0  0  1 ]
              [-1  0  1 ]
              [-1 -1  0 ].

Every off-diagonal symmetric pair cancels except (0,1), whose combined coefficient is -1. Hence this total is -r_0*r_1<0, contradicting the summed score equality. No finite nonuniform quotient supported in H exists.

The Lean proof avoids any assumed formula for class sizes: it transports finite sums through the row/column bijections, symmetrizes T, and uses the strictly negative term supplied by surjectivity at classes 0 and 1. The source's partial-operation bridge is explicit in `Endpoint.no_partial_quotient`: full S forces every option-valued operation entry to have a value; row and column partial injectivity pass to the total operation. The conclusion is the negation of a universal conjecture, not a surrogate finite predicate.

## Formal files and verification

* `Defs.lean`: literal coordinate lines, covering number, arbitrary finite partial quasigroup and surjective block map, restricted support, universal source conjecture, H and the score matrices.
* `Cover.lean`: exact 17/2 fractional-packing certificate and rho(H)=9.
* `Obstruction.lean`: no total quotient for any finite type Q and any surjective class map, with both Latin injectivities proved sufficient.
* `Endpoint.lean`: complete partial-to-total bridge and `Cover377831.source_refutation : not Cover377831.SourceConjecture`.
* `Audit.lean`: all declarations whose actual module origins are the four mathematical modules, including generated/private declarations, with unsafe/local-axiom rejection and transitive axiom checks. There are 35 such declarations in the first successful inventory.

The source definition uses Fin n as a labeling of the arbitrary finite underlying set, and a surjection as a labeling of its partition classes. These are the ordinary finite relabelings, not extra uniformity assumptions. In addition, `no_total_quotient` is itself stated on an arbitrary finite type Q. Source GQPQ support need only be contained in H, which is precisely what the last conjunct requires. No assumption that the quotient support equals H is used.

The source-only ZIP is `377831-proof-packet.zip`; the independent fresh extraction is `fresh-replay/`. Verification status and per-process cap receipts are in `fresh-replay/replay-receipts/`. No full upstream rebuild is claimed: external cached dependency oleans and their exported summaries are trusted. `leanchecker` is from the same Lean installation and is not an independent foundational kernel.

## Bounded novelty and significance investigation

The original conjecture and source definitions were read directly. The source's Theorem 2 characterizes quotient supports by nonuniform integer line marginals; it does not supply the proposed cover-number converse. Its existing example is a GQQ which contains no GUQQ, whereas the present H contains no GQQ at all. Thus that example is not an explicit subsumer of this proof. The present obstruction addresses the full nonuniform claim.

History searches by ID, title and source strings located no previous campaign exclusion for this target. Current public registry HEADs were fetched through `/commits/HEAD`; Omega's changed HEAD required fresh complete D5 and Problems path listings. ID/path screens are not semantic reading of all registry proof bodies.

Dated arXiv API searches include generalized quotient quasigroup, generalized quotients and Latin, GQPQ, covering number and quasigroup, generalized uniformly quotient, and the source title. The relevant retrieved lead is the original 2003 source; no later full resolution was located in this bounded screen. All query results and hash receipts are retained. No MathDB/Palomar access retry, expired general web connector retry, Crossref retry, author contact, upload or publication was performed.

Material limits: publisher version, comprehensive citation graph, non-arXiv papers and all registry proof bodies were not exhaustively reviewed. No worldwide novelty or significance certification is made. A source-faithful Lean counterexample alone is insufficient for credit. Independent review and root adjudication remain required.
