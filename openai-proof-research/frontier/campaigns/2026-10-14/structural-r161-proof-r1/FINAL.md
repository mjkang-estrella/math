# Independent correctness review: PASS

T126S161 / unchanged frozen Structural161 author-proof nominee. Review by Codex / GPT-6 Astra / high / default service tier. No author correctness grade was supplied or adopted. **PASS means the unchanged author proof establishes every frozen conclusion; no mathematical repair is required.** This is a correctness verdict only. No contribution, acceptance or count is assigned; parent alone integrates.

Target: `fresh-structural-discovery-r161/scope-frozen.md`, SHA256 `b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813`. Evaluated proof: `fresh-structural-discovery-r161/author-proof.md`, SHA256 `f522cf05688e557aa7934946ee79564ee55238f0057423135a58c4d9abee451a`. Both are unchanged. All supplied detached author-envelope anchors matched.

## Full-scope conclusion

Let q>=3 and ell>=1 be arbitrary integers, let N>0 be divisible by q, let all s_u be positive integers summing to N, and let all t_alpha be nonnegative integers satisfying sum t_alpha=N/q and sum alpha_u t_alpha=s_u, where alpha ranges over weak ell-compositions of q. Use the uniform spaces and inner products and the block-product projection Pi_d in the frozen statement, with ordinary unnormalized trace. Put

    m(q,r)=binomial(q+r-1,r-1),
    C=ell^q+1+q*ell+q*(m(q,ell^2)+ell^2+1)+2*q*(m(q,ell)+1).

1. Every such table fiber is nonempty, and for every allowed N,s,t,

       tr((T_t^* T_t)^q) <= exp(C)*(N+1)^C.

2. For every real K>0, the EXACT frozen choices

       d=ceil(2*C+4*q*K+2),
       N0=ceil(max(4*d^2,q*d+1,exp(C)*2^(C+d)*d!))

   give ||T_t(I-Pi_d)|| <= N^(-K) for every N>=N0 divisible by q and every allowed s,t.

3. For EVERY integer d>=0, every allowed N,s, every fixed z in Z, and EVERY real f on X, there is ONE real polynomial p_(z,f,d)(t), of total degree at most d, such that (T_t Pi_d f)(z)=p_(z,f,d)(t) simultaneously for ALL admissible t.

Zero table entries, rare conditioning events, arbitrarily unbalanced positive cell sizes, arbitrary real functions without symmetry, d=0 and degrees exceeding N/q are covered as stated. No q=2 theorem, growing-parameter asymptotic, Foulkes assertion or downstream conclusion is added.

## Operative review and objections

The complete independent derivation is [notes/01-mathematical-checks.md](notes/01-mathematical-checks.md). Locations below refer to the authenticated author proof.

* Lines 12,20-67,105-136: exact incidence normalizations and ordinary cyclic trace agree; every compatible joint block table has the required P,P tuple marginals and R coordinate marginal. The factorial remainder bounds retain their signs at zero entries. Summing types gives the EXACT stated C.
* Lines 73-99: data processing gives J_i>=I_i separately, and the average of the q deleted-edge path inequalities gives TC>=(q-1)/q sum I_i. This cancels the entire trace exponent without any globally consistent choice of the maximizing Q_i. The potential compatibility objection does not occur.
* Lines 140-157: the fixed-vertex equivalence relation determines the orbit; every nonzero orbit-indicator monomial uses disjoint blocks, each containing at least two fixed vertices. Branching exclusions, the unused-block transposition killing sign, and the explicit standard-tableau construction give dimension >=N^(d/2)/(2^d d!) under exactly the supplied thresholds.
* Lines 161-186: compression eigenvalue interlacing works even when A and Q do not commute. The top eigenspace dimension and qth trace imply the frozen norm estimate, with the stated d and N0 absorbing every factor. No multiplicity-free assumption is hidden here.
* Lines 190-201: the exact falling-factorial containment formula has a strictly positive denominator independent of t. A real expansion of Pi_d f can be fixed before t varies, establishing one polynomial for all tables and all real f.

No unresolved mathematical objection, missing compatibility lemma, changed constant, restricted quantifier or proposed repair remains. The qth/second-moment diagnostic and finite programs were inspected as evidence, not premises.

## Dependencies, evidence and limits

Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative upstream proofs remain stipulated true. The actual complete q=2 smoothing source body was read and authenticated, but it was not used to assume the q>=3 transfer. The new steps above were checked independently. Symmetric-group branching and tableau facts were read in the actual Vershik-Okounkov primary body, including fresh inspection of PDF pages 22-24; the entire paper was not read. Entropy and factorial inequalities were derived directly, so no unread primary entropy theorem is a dependency.

The 46 author table cases and six spectral outputs reproduced exactly. Independent finite checks covered 156 table/size cases, 4024 containment probabilities and 210 joint block tables. They do not establish universal claims. All mathematical read extents, recovered display truncation, isolation limits and dependency boundaries are in [notes/02-evidence-and-limits.md](notes/02-evidence-and-limits.md). No required source read failed. I199/I202 originals were followed narrowly; their targets and dispositions are unchanged.

This review is sealed once with its OWN exact selected manifest, excluding the three root envelopes FINAL.md, MANIFEST.json and REPORT.md. Three independently calculated detached SHA256 anchors accompany the handoff. [tools/verify.py](tools/verify.py) is read-only and checks artifact integrity, not mathematics. Incoming originals, private derivatives and reduced-copy membership remain separate under original rights. No author file was edited and selected original bytes/modes remained stable.
