# H003 fixed-window EDS character collapse: raw independent review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h003-eds-character-collapse-review-opus-20261008-r1`
Claude Opus 5.5, read-only; no experiment or child reported.
Reviewer generalizations and exclusions are not automatically accepted; see disposition.

I've read the four files and the primary paper. **Verdict: I agree with the derivation and the bound, with a few repairs and one real gap.** I found no counterexample. The scoped conclusion holds: for fixed offsets with small s, the A1 predictor family cannot meet H003's sufficient threshold. It is not a lower bound for scalar recovery in general.

## 1. Source: exact statement
Source: Shparlinski–Stange, "Character Sums with Division Polynomials", arXiv:0912.5246v4 (5 Jun 2011), §4, p. 4. In the paper, q is the **field size** and the characteristic is p>3.

- **Lemma 4:** η is a non-principal multiplicative character, K=F_q(E), and f∈K has degree d with "f ≠ g^m for any function g in the algebraic closure K̄ of K and m | q−1". For any ω∈Ω=Hom(E(F_q),C*), |Σ*_{P∈E(F_q)} ω(P)η(f(P))| ≤ 2d√q. Σ* means the sum skips points where f(P)=∞.
- **Lemma 5:** the same bound over any subgroup H⊆E(F_q). The proof averages over characters trivial on H.

Caveats on the source:
- Lemma 4 is introduced as "essentially [1, Proposition 1]", i.e. Chen, Monatsh. Math. 154 (2008), which "in turns comes from" Perret, Acta Arith. 59 (1991). Chen states it for prime fields only, which is our case. The paper does not prove Lemma 4, and **I did not check Chen or Perret**. Cite this as a secondary statement.
- Read literally, "g in the algebraic closure K̄ of K" makes the hypothesis vacuous: every f is a square in an algebraic closure of the function field. The intended meaning is F̄_p·K, i.e. f is not a constant times an m-th power over F̄_p. With that reading, m=1 is excluded, as intended.
- For a prime-order curve, H=E(F_p), so Lemma 4 applies directly and Lemma 5 is not needed.

## 2. Derivation check
- **Doubling identity.** Set n=2 in the corrected identity, with l=p−1 and l′=l+q. Then l′²−l² = q(2p−2+q) ≡ q² (mod p−1), so φ(2T) = φ(T)^4·W_T(2). For short Weierstrass, W_T(2)=ψ₂=2y; the code agrees (`eds_diagnostic.py:248`, `w2 = 2*y`).
  - y(T)≠0 because T has odd order q and is not the identity.
  - χ(φ(T))^4=1, so χ(φ(R)) = χ(2y(R/2)) for every R≠O. R/2 = ((q+1)/2)R is the unique half of R inside ⟨G⟩.
  - Cross-check: the exponent inv(q²) mod (p−1) is odd, so χ(φ(R)) = χ(W_R(p−1)/W_R(p−1+q)) directly.
- **c and CM.** The formula is pointwise and never uses c=χ(φ(G)), so it covers c=±1. Neither CM nor j∈{0,1728} enters. Supersingular curves are excluded automatically: #E=p+1 is even.
- **Pullback issue (real, and avoided).** As a function of R=kG, y(R/2) is *not* in F_p(E); it lives on the [2]-cover. The variable must be S=kH. The map k↦S just re-indexes the group, and ω(S)=e_q(−a·log_H S) is a genuine character of E(F_p). Any write-up must state this.
  - Lemma 4's proof (Lang-isogeny cover) pulls f back along a separable, unramified map, so simple zeros stay simple. This also holds when q=p (anomalous), since d(Frob−1)=−1.
- **Divisor of f(S)=∏_{j∈A} y(S+jH).**
  - Zeros: the sets E[2]*−jH. They are disjoint because e−e′=(j−j′)H would lie in E[2]∩⟨G⟩={O}.
  - Zeros never meet poles, by the same argument.
  - Poles: −jH, each of order 3, all distinct mod q.
  - So f has 3s simple zeros (all off ⟨G⟩) and degree d=3s. It is not c·g^m for any m≥2.
- **Zeros and poles on the summation set.** f has no zeros on ⟨G⟩. Its poles in ⟨G⟩ are exactly the identity windows k≡−j, which Σ* omits and B=0 assigns. The two conventions match exactly, with denominator q.
- **Normalization.** χ(2^s) is a unimodular constant.
  - |B̂(a)| ≤ (1/q)·2·3s·√p = 6s√p/q for **all** a, including a=0.
  - Parseval gives |corr| ≤ max|B̂|·‖ĝ‖₁ ≤ 6s√p(2+ln q)/q, using the ‖ĝ‖₁ bound already accepted in H003.
  - The genus/ramification count suggests 4s√p (4s points of odd order), but that is unverified. Keep 6s.
- **p/q exceptions.** We need p≥5, q≥5 prime and gcd(q,p−1)=1; q=p is allowed but is anomalous and already easy. The bound is nontrivial only when s < q/(6√p) ≈ √q/6. At the tiny sizes the bound is trivial (q=139, s=1 gives a coefficient bound ≈0.49), so the observed 30/139 ≈ 0.22 creates **no tension**. The tiny data neither supports nor refutes anything.
- **Size check.** At p≈q≈2^256 with s=5, |corr| ≲ 2^−115.6.

## 3. Scoped conclusion I would accept
Take a prime-order E/F_p (p≥5), fixed distinct offsets A mod q with |A|=s, and B_G=∏χ(φ) with B=0 on identity windows. B equals χ(2^s∏y(kH+jH)), and every normalized Fourier coefficient has magnitude ≤ 6s√p/q. Hence |parity correlation| ≤ 6s√p(2+ln q)/q.

- **What follows.** For s ≤ q^{5/12−δ}, ε=O(s·q^{−1/2}·log q) eventually violates H003's sufficient condition β<1/12. The "heavy coefficient" alternative fails the same way.
- **Generalization.** The bound extends to any fixed decision function F applied to the window bits. Expand F into subset products A′⊆A: the result is ≤ (Σ|F̂(A′)|)·6s√p(2+ln q)/q + O(s/q), where O(s/q) covers the identity windows. This covers learned selectors and majority votes for s=O(log q).
- **Simplification.** A1 reduces to an elliptic Legendre-type sequence χ(∏y). Pointwise, no EDS structure is left to exploit.

## 4. What does NOT follow, and remaining gaps
1. **No lower bound** for scalar recovery, other recovery algorithms, adaptive or related-point queries, or EDS functions outside this fixed-offset product family. The result shows that one upper-bound construction misses its own sufficient threshold.
2. **Large-s gap (genuine).** For s ≳ q^{5/12}/polylog, the bound no longer excludes H003's threshold, and for s ≳ √q/6 it becomes trivial.
   - Evaluating B costs Θ(s) only under naive evaluation. Structured A could make the degree-3s function cheap: functions like ψ_m∘ have degree ~m² yet are evaluable in O(log m).
   - With naive cost, H003's own work is ≳ s·m ≳ q²/(polylog·s³), which leaves at most polylog-level room. With structured cheap evaluation, the regime is open.
   - Also unexamined: the degenerate full-group product (A = all of Z_q, making B essentially constant).
3. **Heuristic only.** Even an ideal ε^−2 heavy-coefficient finder would face roughly max(s, q/s) ≥ √q. This is not proved; no query lower bound for SFT is established here.
4. Chen/Perret were not read directly, and the K̄ wording needs the repaired reading above.
5. No numerical check of χ(φ(R))=χ(2y(R/2)) was run against the stored JSON. That would be a cheap consistency check if the team wants one.

I made no edits. My only scratch was the downloaded PDF and its text extraction in `/tmp/ssrev`.

Sources:
- [Shparlinski–Stange, arXiv:0912.5246v4](https://arxiv.org/abs/0912.5246), §4, Lemmas 4–5
- Cited, not read: Chen, Monatsh. Math. 154 (2008) 1–10; Perret, Acta Arith. 59 (1991) 279–290
