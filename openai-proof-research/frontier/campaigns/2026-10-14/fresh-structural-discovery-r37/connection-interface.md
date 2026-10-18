# The same-budget equivariant connection remains unpaid

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0. This records specific failed shortcuts, not impossibility of the full RC factor-two target.

The source `03-layers.tex`, `04-connections.tex`, and `05-processing.tex` were read again in full during this supplement. Together with the earlier full source reading, these are actual construction comparisons. No additional literature search or primary theorem read has yet been performed in r37; the primary8/3 operation comparison remains the bounded one in r36.

## Paired initial walks do not yield paired identical sorted profiles

The symmetric base graph has balanced degrees and even outdegree at fixed vertices. Pair incoming/outgoing transitions at each nonfixed vertex and force the reversed pairing at its partner. At each fixed vertex, identify incoming edges with the reversals of outgoing edges, pair the outgoing edges by a fixed-point-free involution, and use those pairs for transitions. There is no fixed transition. The resulting edge-cycle decomposition comes in distinct tau-reversed pairs: a reversed fixed cycle would have a fixed edge or a fixed transition, neither of which exists.

For a self-reversed primitive text of period p, these paired closed walks imply an even total number of primitive passages, since each pair contributes2P/p. This survives sorting as an even number of layers in that text group. It does **not** imply even multiplicity of each sorted profile.

Exact smallest saved example: identity complement and input `bbcbbc`. The symmetric count recursion yields

m(b)=4, m(c)=2;
m(bb)=m(bc)=m(cb)=2;
m(bbc)=m(bcb)=m(cbb)=2;
m(bbcb)=m(bcbb)=m(cbbc)=2;
m(bbcbb)=2, m(bcbbc)=m(cbbcb)=1;
m(bbcbbc)=m(cbbcbb)=1.

The base up-cost is6. Its tau-paired walk decomposition sorts into two period3 layers over A=(bbc)^Z, with exit profiles

z_low(0,1,2)=(5,5,6),
z_high(0,1,2)=(6,6,8),
z_i(x+3)=z_i(x)+3.

Each profile occurs exactly once. The lower layer has up edges at `bbcb`, `bbcbb`, `cbbc` and down edges at `bbcbb`, `bcbb`, `cbbc`. The upper has up edges at `bbcbbc`, `cbbcb`, `cbbcbb` and down edges at `bbcbbc`, `bcbbc`, `cbbcbb`. These are individually reversal-invariant edge multisets. Both are unrooted. They share the fixed vertices `bbcbb` and `cbbc`, so their joint parity is even even though their profiles differ.

`minimal-profile-certificate.json` supplies all counts, profiles and edge multiplicities; `explore.py` reproduces the paired transition decomposition and source sorting. This example refutes the inference from global fixed-vertex parity to even multiplicity of each sorted profile. It does not refute a pairing of connected blocks: the two layers are already connected, and a cost3 root loop through `bbc` together with its mirror through `cbb` connects the block at total cost6, exactly its two budgets.

## Connected fixed-layer blocks still need contacts to other rooted pieces

A direct mirrored round-trip-to-empty budget test also fails. For the single fixed input `ababa`, the symmetric recursion gives

m(a)=4, m(b)=2,
m(ab)=m(ba)=m(aba)=m(bab)=m(abab)=m(baba)=m(ababa)=2.

There are two rooted period1 layers at `a`, and two identical period2 layers with z(0,1)=(5,5), containing vertices `aba`, `abab`, `ababa`, `baba`. The latter block has total budget4 and shortest vertex length3. Thus2·minwordlength=6 exceeds its budget4. This exact certificate is `minimal-short-block-failure.json`.

Again the actual connection is affordable: attach through the already-rooted word `a`. A round trip from `aba` down to `a` and back has cost2; its mirrored copy has cost2. The total4 fits. This demonstrates the need for the source's cross-text/host mechanisms; it does not exhibit a budget obstruction for the full construction.

## A fixed layer's single budget does not automatically pay mirrored prescribed contacts

There is a precise local failure of simply reflecting an ordinary individual link at unchanged cost. Use A=(ab)^Z, period p=2, identity complement. Let C be the one-turn layer with z(0,1)=(4,5), extended by z(x+2)=z(x)+2. Its windows have lengths3 and4, and its up and down words are `abab` and `baba`. Its edge multiset is tau-fixed.

Take the prescribed record R=[0,6), word `ababab`, so rho(R) has word `bababa`. This record can agree with A inside another periodic text; no claim that its host is the same primitive group is needed. The source individual-link hypotheses hold:

f_C(0)=3<=b=6,
l_C(0)+p=4+2=6,
and all layer word lengths exceed p.

The ordinary source loop through R, [2,6), R+2 has up-cost2 and touches C at `abab`. It cannot simply be replaced by a tau-invariant added closed-walk family of up-cost2 touching C and the same prescribed record. Any balanced component of such a family that touches a length6 vertex and C must bridge word lengths6 and at most4. With total up-cost2, its Euler walk has exactly two up and two down steps. Achieving a range of2 forces the two downs and the two ups consecutively, so it has exactly one maximum-length vertex. Tau-invariance would require both distinct length6 words `ababab` and `bababa` in that same component: C is tau-invariant and all the available budget is already in the component connecting C to R. This is impossible. Splitting into separate cost1 components cannot bridge the length difference2.

This is a local prescribed-contact obstruction only. C by itself violates the even fixed-vertex condition at its two odd-length palindromes, so a valid symmetric base graph must supply additional incident material. That additional material may pay the mirrored connection. Consequently this observation supports a connected-block/host-budget argument rather than refuting one. It also shows why constructing a reflected half-period path must prove that all required contacts fit its monotone window chain; the one-sided source clamps do not make that automatic.

## Exact remaining proof obligation

A successful full construction must connect the symmetric base graph to empty, preserving tau and even fixed-vertex outdegrees, at added up-cost at most W_sym. The source's period budgets, recorded occurrences and count rules remain available. The unexplained step is an algorithm assigning paired/folded layer or connected-block budgets to equivariant collective links, host excursions and cycle opening, including self-reversed primitive texts. A dihedral maximal rotation controls comparison with either target orientation but does not assign these budgets.

The parent suggested processing components of self-fixed layers that already meet at fixed words, and reflecting a half-period host path whose two endpoint windows lie on reflection axes. Both remain plausible directions. One must prove the full monotone contact order, membership of intermediate words in V, the charge for variable periods and all incoming host requests, and preservation of global budget disjointness. The examples above show where simple independent-layer and direct-root shortcuts stop.

Retaining the symmetric base once and adding an ordinary source connection B together with tau(B) gives total up-cost at most3W_sym. The half-Euler interface would then give a technical3-approximation, worse than the primary8/3 result. Duplicating the whole base plus connection would instead give4. Neither is counted or presented as the target.

Status remains **UNRESOLVED**. There is a proved count-budget interface and a half-Euler graph lemma in `counts-and-euler.md`, subject to independent review, but no same-budget equivariant connection and hence no full factor-two algorithm. No candidate freeze, novelty claim, acceptance, Lean compilation or external action is asserted.

Later necessary-condition test: budget-counterexample.md supersedes the merely-unpaid classification of the proposed global same-budget extension. That statement is false, with W_sym6 and OPT_RC7. The full factor-two target remains unresolved.
