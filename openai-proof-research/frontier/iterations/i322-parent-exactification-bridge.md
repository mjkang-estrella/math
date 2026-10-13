# I322 parent bridge — exactification from a witness-computable success law

2026-10-13. **Technical bridge, unreviewed; no acceptance.** This isolates a possible use of the pinned factoring paper's dyadic completion. It does not construct the required discrete-logarithm trial or its success formula. Those remain the hard part of I322.

## Hypotheses

For each promised classical input x of length n, a polynomial-time classical verifier accepts exactly one L(n)-bit string y=f(x). Padding makes L a known polynomial bound with a unique canonical encoding. A bounded-time quantum procedure A over the pinned fixed gate set outputs a candidate. Its probability p(x) of passing verification is at least 1/q(n), for an explicitly known positive integer polynomial bound q. Given x and its valid y, an ordinary deterministic polynomial-time algorithm computes p(x) exactly as a dyadic with polynomial bit length. It need not compute p from x alone. The procedure, verifier and probability computation all have uniform polynomial worst-case resources.

The explicit dyadic assumption is essential. No claim is made that every probability of a circuit with controlled Hadamards is dyadic, or that a generic quantum circuit's success probability can be efficiently computed.

## Conclusion and proof

A uniform polynomial-size quantum circuit over the same fixed set, with the inverses and controlled versions already present in the source model, outputs f(x) with probability one.

Run A independently R=2q(n) times on fresh registers, verifying each output, and retain the first valid candidate, all histories and a success flag. On the promised input the candidate is always y when valid, and the success probability is

    P=1-(1-p)^R >=3/4.

Indeed (1-1/q)^q<=1/2 by 1-1/q<=1/(1+1/q) and (1+1/q)^q>=2; the case q=1 is immediate. This lower bound uses no approximate arithmetic. P is computable exactly from (x,y) with polynomial dyadic representation, by integer powering, once a valid y has appeared.

Let J=L+2. On valid (x,y) compute

    C=2^(-J) floor(2^J/(2P)),
    e=1/4-PC/2.

Then 0<=C<=1 and 0<=e<P*2^(-J-1). In a branch chosen with probability 1/2, run the amplified procedure and, if valid, retain its flag with probability C. In the other branch, guess a uniform L-bit y, check the verifier, and on the unique valid guess retain with probability 2^(L+1)e. On invalid guesses compute any fixed dummy arithmetic values and reject. The latter valid retention is less than P/4<=1/4, and every actually sampled probability is a polynomial-bit dyadic. The required divisions are only reversible integer divisions for a floor, never an exact non-dyadic coin.

The two successful masses are respectively PC/2 and

    (1/2)*2^(-L)*2^(L+1)e=e,

so the preparation succeeds with probability exactly 1/4. Both branches output the same y on success. Although the circuit does not know y in advance, the exact P computed on either successful branch is identical by uniqueness. This is the only place witness-computability replaces initially known probability.

Use the pinned retained-classical-records construction to implement the preparation as a uniform unitary V_x, keeping old histories orthogonal and without copying quantum data before required interference. Reflection about its input state is V_x times the all-zero reflection times V_x inverse; reflection about the success flag is exact. One ordinary Grover iteration takes success amplitude 1/2 to one (rotation from pi/6 to pi/2). The good subspace is supported only on the canonical verified y, so the classical output is f(x) with certainty. All records, repetitions, arithmetic bit lengths, multi-controlled reflections and gate lists have polynomial worst-case bounds, including failed histories. No postselection is performed.

## Scope and attribution

The quarter-success arithmetic and exact amplification are applications of the pinned paper's Sections 2 and 6, not new inventions. The paper makes its final factoring preparation probability known; this formulation allows the original trial's probability to become computable only from the unique accepted output. The parent regards the argument as a technical compiler lemma, not a substantial finding. It does not turn every bounded-error uniquely verifiable problem into an exact one: efficiently computing its exact dyadic success law from a witness is an additional, potentially hard hypothesis. Nor does probability-one correctness alone give a polynomial worst-case bound without the explicit clocks assumed above.

Primary source: `preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/build/sections/02-model.tex`, lemmas dyadic and records, and `06-exactness.tex`, lemmas completion and quarter, at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The parent read the complete 39-line model, Section 6 lines 9-27 and 94-116, and the deferred-filter proposition 50-72; it has not yet read all later exact-amplification paragraphs. Those paragraphs are not represented as newly verified source evidence. I322 must read the full relevant source and independently check this bridge before using it.
