# Family 148: countable-alphabet feasibility, before any scope freeze

This is a pre-freeze operation screen, not a nominated full theorem or independent PASS. The potential extension of the exact finite-family entropy-rate formula appears TECHNICAL: the decisive entropy-growth and disjoint-window operations are already source-paid. The observations below identify why merely changing finite to countable is not a substantial new mechanism. No frozen target has been narrowed.

## 1. Type entropy is sublinear

Let I_1,...,I_b be iid on a countable alphabet with H(p)<infinity, and T_b their multiset. For a finite alphabet subset F, record the counts of symbols in F and the sequence Z_j that equals I_j outside F and one marker inside F. This record determines T_b. Therefore

H(T_b) <= |F| log_2(b+1) + b H(Z_1).

Writing delta=p(F^c), H(Z_1)=-(1-delta)log_2(1-delta)+sum_{i outside F} -p_i log_2 p_i, which tends to zero as F increases to the alphabet. First let b tend to infinity, then F increase. Thus H(T_b)/b tends to zero. This elementary tail encoding replaces the source's m log(b+1) bound. It does not assert continuity of random-walk entropy under finite-alphabet truncation.

## 2. Conditional supports have a factorial bound

Given a length-b type, at most b! distinct orderings remain. This holds regardless of the total number of possible symbols. The conditional law is uniform on the b!/prod k_i! orderings, since their iid probabilities agree. Each conditional block translation therefore has support D_kappa of cardinality at most b!. After n types are fixed, all signed contraction products R_j are fixed, and the prefix support S is contained in sum_{j<n} R_j D_{kappa_j}. Consequently

log_2 |kS| <= n b! log_2(k+1).

No common finite union of the D_kappa is required. The same conditional-word count gives H(nu_{omega,n}) <= n log_2(b!), a uniform bound sufficient for discarding the event of atypical accumulated contraction. This is exactly the source's sumset-counting operation with the correct conditional alphabet, not a new inverse-entropy theorem.

The type space is countable. For each environment the conditional prefix has finite support, but there need not be a deterministic cutoff containing every pair separation. Since the pair terms are nonnegative, monotone convergence permits a finite cutoff B_n that retains half the available expected pair mass. The source's later argument needs only a finite cutoff with a positive linear expected bound, not supportwise equality of truncated and full sums. Countable measurable choices of pair maximizers are immediate by enumeration.

## 3. Finite-mean contraction substitutes for the deterministic window bound

Let Y_j>0 be iid block contraction depths with finite mean m=b chi. For fixed candidate start j <= T/(4m), Markov gives P(sigma_j<=T/2)>=1/2. This prefix event is independent of the future block's pair mass and of its good-increment event. Add the prefix event to the source retention rule. Every retained pair depth then still occurs among target depths 1,...,T, and each band contributes at least a fixed positive multiple of T. Pathwise disjointness and telescoping are unchanged. This is a first-moment truncation, not a new window arrangement.

## 4. The stopping overshoot is uniformly tight under finite mean

For a uniformly contracting family, put c=-log_2 sup_i |r_i|>0 and take iid one-symbol depths Y_j>=c with E Y_j<infinity. Let S_j=sum_{k<=j}Y_k and tau_x=min{j:S_j>=x}. For M>0,

P(S_{tau_x}-x>M) <= sum_{l>=0} P(Y_1>M+l c), uniformly for x>0.

Indeed, split possible preceding positions S_j<x according to x-S_j in [lc,(l+1)c). Since successive positions are separated by at least c, each half-open strip contains at most one S_j on each path; independence of the next increment gives the displayed union bound after expectation. The right side tends to zero as M tends to infinity because E Y_1 is finite. Thus no second moment or bounded lower contraction ratio is necessary for tight overshoots.

In the source's nonsaturation argument, discard the overshoot event of probability at most eta. On its complement the scale distortion is at most 2^M, so the original integer-window concavity gives at least (1-eta)[G_{v,Kv}(mu)-C_M], with C_M independent of K. First choose eta with 1-eta>d, then M, then K large. The source contradiction is preserved. This uses the same stopped-mixture transfer and a standard integrable-tail estimate.

## 5. A necessary entropy boundary

Finite H(p) cannot be silently discarded in an entropy-rate formula defined by H(G_n)/n. Choose countably many distinct contraction ratios in [1/3,1/2] whose logarithms are rationally independent and a probability distribution of infinite entropy. All maps x -> r_i x have common fixed point zero, so their stationary measure is delta_0 and has dimension zero, while chi is finite. Rational independence means a product identifies the multiset of n symbols. Given that multiset, at most n! ordered words remain; the multiset entropy is infinite because the word entropy is infinite and its conditional entropy is at most log_2(n!). Hence H(G_n)=infinity for every n. This is a diagnostic against an unqualified infinite-entropy transfer, not a substantial counterexample nomination.

## 6. Actual comparison and read limits

Pinned source148 introduction.tex, entropy.tex, types.tex and windows.tex read completely. Its pairs.tex, corollaries.tex, main.tex and references.bib were retrieved but not yet read completely. The finite-law pair theorem is therefore referenced through its explicit invocation in types.tex, not represented as independently reviewed in this screen. All nine non-PDF source files match complete-tree Git blobs; source148-receipt.json records identities.

Mihailescu–Urbanski, Random countable iterated function systems with overlaps and applications, arXiv:1405.2942v2 (23 March2015; current primary version page checked), actual extracted lines177–269 and983–1153 read. Definition2.2 assumes a common contraction constant and conformal extensions to a bounded common neighborhood; Definition2.4 uses projection entropy. Theorem3.13 and Corollary3.14 give exact dimensionality and the projection-entropy/Lyapunov formula under finite conditional symbol entropy. The actual proof ending transfers cylinder-radius limits via a K-perturbed scale sequence and lets K decrease to one. The predecessor lemmas establishing those cylinder limits have not been read here, so this is a bounded operational comparison, not a full proof audit. Its projection entropy must not be identified by definition with complete affine-map random-walk entropy. The source supplies the hard comparison for finite alphabets; the modifications above are tail/counting adaptations of its proof.

A guessed v3 PDF request returned404; primary arXiv version history established v2 as latest. The v2 PDF and text are private and hashed. No worldwide novelty or full historical clearance is claimed. No target is frozen and no complete countable-family theorem is certified by this feasibility note.

Original prose: Myeongjin Kang, no affiliation, CC BY4.0. Third-party files private.
