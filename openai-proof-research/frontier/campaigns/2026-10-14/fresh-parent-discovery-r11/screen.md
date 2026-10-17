# Preliminary circular trace screen

Myeongjin Kang; 2026-10-17. Original prose CC BY 4.0, original code MIT.

Status: exploratory source-family122 screen, **no frozen target, nomination or acceptance**. The full quasipolynomial circular reconstruction theorem is not proved here. Source truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. This screen checks a new deduction interface, not upstream truth. Uploads remain stopped; campaign count remains10/20.

## Channel correction and exact elementary conversion

Let x be a binary word of length n and p>0 the retention probability. The circular channel C_x deletes each coordinate independently and then chooses a uniformly random cyclic root of the surviving output. This is the model in Burudgunte–Valiant–Wang, *New Bounds for Circular Trace Reconstruction*, ITCS2026, Definition4. Empty output is unchanged.

This differs from choosing a uniform cyclic root of the input and then running ordinary deletion. For x=0011 and p=1/2, the latter has probabilities3/64 and1/32 for outputs001 and010; C_x gives1/24 for both. The included rational enumeration reproduces this exactly. Consequently, one cannot import ordinary trace reconstruction by simply treating circular samples as a uniform mixture of ordinary rooted traces.

There is a valid conversion. Accept a circular output t of length l with probability l/n, rejecting the empty word. The acceptance probability is p. The resulting conditional law Q_x is obtained by choosing an input root uniformly, forcing that root to survive, and deleting the remaining n−1 coordinates independently with probability1−p. In particular,

    Q_x(t) = |t| C_x(t)/(np).

Proof: for a nonempty survivor set S, C_x assigns weight p^|S|(1−p)^(n−|S|)/|S| to each rooted survivor word with root j∈S, counting multiplicities of equal words. Acceptance cancels |S|, and conditioning divides by p. The resulting term is n^−1 p^(|S|−1)(1−p)^(n−|S|), exactly the forced-retained-root construction. Summing |t|/n against C_x gives E|S|/n=p. This is an elementary identity, not a contribution nominee.

For two length-n words, the empty-output probabilities agree. Thus the identity also gives

    p TV(Q_x,Q_y) ≤ TV(C_x,C_y) ≤ np TV(Q_x,Q_y),

by multiplying each nonempty Q difference by np/|t|. This compares the circular and forced-root mixture problems; it does not solve either one.

## What input-coordinate separation supplies

For any finite set of m distinct binary words, some word can be isolated by a product of at most floor(log2 m) coordinate literals. At each stage select a coordinate that varies and keep the smaller nonempty branch, until only one word remains. For the union of two distinct cyclic orbits, m≤2n. The resulting cylinder has expectation at least1/n under one uniform orbit law and0 under the other. Expanding its literals yields some ordinary coordinate monomial with expectation discrepancy at least1/(n2^D), D≤floor(log2(2n)).

This elementary selector is neither a novel contribution nor an observable statistic of a deletion trace with controlled variance. The primary circular-trace paper has a stronger order-at-most6 cyclic-moment separation for integer sequences (Lemma19). Its sparse-string algorithm conditions on all k ones surviving and uses shifted-gap cyclic moments; for constant k this event costs only a constant depending on p,k. That conditioning costs p^k for dense strings and does not by itself supply arbitrary-density quasipolynomial reconstruction.

## Exact unresolved source interface

The pinned uniform ordinary-trace source separates a positive Boolean functional with a wrong fixed prefix from a *single evaluation* at x. Its multiscale proposition assumes Δ=E−eval_x, with Δ[X_i]=0 before the first wrong coordinate and a unit discrepancy there. This prefix agreement is used to remove negative powers in the generating sum.

More essentially, multiscale.tex, Lemma `balanced-product`, uses

    |E[A(t)]|² ≤ E[|A(t)|²] ≤ |A(t)(x)|² + ε.

The normalized intermediate polynomials all evaluate to1 at the same x. Hence their norms and adjacent inner products are close to1 in the Hilbert space induced by E, permitting the Gram-chain argument. Replacing eval_x with a uniform orbit mixture does not preserve this rank-one factorization. A difference of two positive functionals is not enough to invoke the proposition unchanged. Pairwise separation of pure rooted words also does not prevent cancellation in mixtures.

An input selector could condition the true orbit measure to one word. But multiplying by that selector does not yet supply a bounded-variance observable of circular deletion outputs, nor the source's fixed-prefix condition for the competing functional. Establishing quantitative mixture separation with the required degree, decay, coefficient and sample bounds remains unpaid. No claim of impossibility is made; no smaller substitute is nominated.

## Sources and reading limits

Eight pinned blobs and two primary PDFs are locally authenticated in source-receipts.json and primary-receipts.json. Third-party bodies stay private and are not intended for staging or publication.

- Source `Uniform-quasipolynomial-time-trace-reconstruction-October-5-2026`: main.tex lines1–184, setup.tex1–163, separation.tex1–548 read in full as text; multiscale.tex1–175 and255–398 read. Figure TeX was read, not rendered. contour.tex, decoding.tex, history.tex and references.tex were retrieved but not read. These limits do not claim a full source proof audit.
- Burudgunte–Valiant–Wang, [ITCS2026 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/LIPIcs.ITCS.2026.30/LIPIcs.ITCS.2026.30.pdf): extracted lines1–260,280–375,625–690,790–1040 read, including channel definitions, Lemma19 proof, Algorithm1, Theorem26 proof and Lemma28 proof. Lemma19 invokes prior lemmas whose complete proofs have not been read. The lower-bound section opening was read, not its full argument. No independent full-paper verification is claimed.
- Narayanan–Ren, [ITCS2021 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol185-itcs2021/LIPIcs.ITCS.2021.18/LIPIcs.ITCS.2021.18.pdf): retrieved, body not yet read.
- History I152 lines80–150 read: its developed heterogeneous known-retention target differs, and remains unpaid there. Initial broad search output was truncated; it is not a complete developed-history eligibility check. No eligibility verdict is issued here.

The source's pinned ordinary reconstruction result includes sample and bit-work bounds; neither is established for the circular problem here. Exact finite diagnostics verify only the stated small-channel identities. They do not prove reconstruction, substantiality or worldwide novelty.

Further parent calculation: [mixture-obstruction.md](mixture-obstruction.md) gives explicit parity-binomial laws for which the initial scale signal survives but every balanced product of at most four Gaussian-window factors falls below the scale-step threshold. These are not uniform cyclic-orbit laws. This rules out a generic positivity-only replacement, not the circular reconstruction target.
