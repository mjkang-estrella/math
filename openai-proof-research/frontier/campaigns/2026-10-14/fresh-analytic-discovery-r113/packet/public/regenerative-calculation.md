# Finite-information calculation for regenerative affine products

These are disclosed pre-freeze feasibility calculations. They are not a nomination, a full dimension theorem, an independent proof gate, or a claim of new priority. The central exact estimate is elementary information theory plus group cancellation; the regenerative construction is credited to the primary source below.

## 1. An exact clock comparison that does not see word boundaries

Let A be a finite alphabet of size m>=1 and assign each letter an invertible element g_a of a group. Real similarities with nonzero signed contraction are the application. On ANY probability space let (I_j)_{j>=0} be an A-valued process, with arbitrary dependencies, and define G_n=g_{I_0}...g_{I_{n-1}}, G_0=1. Let S,T be nonnegative integer-valued random variables, not necessarily stopping times. Assume H(S,T)<infinity, E(S+T)<infinity. Logarithms are base two.

Then all product entropies are finite and

    |H(G_S)-H(G_T)| <= H(S,T)+E|S-T| log m.                 (1)

Indeed H(G_S)<=H(S)+ES log m. Given S,T and the intervening ordered word V=(I_min(S,T),...,I_max(S,T)-1), one product reconstructs the other. If S<=T then G_T=G_S g_V and G_S=G_T g_V^(-1). If S>T reverse the roles. Conditioned on S,T, there are at most m^|S-T| possibilities for V, even if those clocks depend on all the symbols. Thus H(V|S,T)<=E|S-T|log m and both conditional entropies H(G_S|G_T), H(G_T|G_S) are at most the right side of (1). Their difference is H(G_S)-H(G_T). This proves (1).

Equal group products may identify many words, of different lengths or with different hidden marks. The argument never inverts the word-to-product map. It cancels a KNOWN intervening product. Consequently exact affine-map collisions, negative contractions, and unobserved regeneration boundaries cause no additional term.

For a nonnegative integer N of mean a<infinity,

    H(N) <= (a+1)log(a+1)-a log a <= log(e(a+1)),           (2)

with the usual convention at a=0. Compare its law with the geometric distribution of mean a: nonnegativity of relative entropy gives the first bound, first for finite truncations and then by monotone entropy approximation. The second follows from a log(1+1/a)<=log e. This provides an explicit logarithmic clock charge from first moments alone.

## 2. Delayed iid word representations

Suppose the one-sided symbol process is represented as a finite initial word A_0 followed by iid nonempty finite words B_1,B_2,... . Allow dependence between A_0 and the subsequent words for the inequality below; their marginal iid law is enough. Let L_i=|B_i|, ell=EL_1, Z_k=g_{B_1}...g_{B_k}, and T_k=|A_0|+sum_{i<=k}L_i. Assume H(A_0)<infinity, E|A_0|<infinity and EL_1^2<infinity. Let n_k=floor(k ell).

The exact identity G_{T_k}=g_{A_0}Z_k implies

    |H(G_{T_k})-H(Z_k)| <= H(g_{A_0}) <= H(A_0).           (3)

It needs no independence: either group variable reconstructs from the other and g_{A_0}. Also

    E|T_k-n_k| <= E|A_0|+sqrt(k Var L_1)+1,
    H(T_k) <= log(e(E|A_0|+k ell+1)).

Equations (1)-(3) give the explicit bound

    |H(G_nk)-H(Z_k)|
    <= H(A_0)+log(e(E|A_0|+k ell+1))
       +(E|A_0|+sqrt(k Var L_1)+1)log m.                  (4)

No renewal event has been asserted to be a forward stopping time. That would be wrong for the CFF global regeneration event; (1) deliberately does not need it.

If the symbol process is stationary, H(G_{n+r})<=H(G_n)+H(G_r), because the suffix product has the law of G_r and joint entropy is at most the sum. Thus h=lim H(G_n)/n exists. The iid word products likewise have h_word=lim H(Z_k)/k, provided H(g_B1)<infinity. This holds because H(B_1)<=H(L_1)+ell log m. Dividing (4) by k proves

    h_word = ell h.                                     (5)

For similarities phi_a(x)=r_a x+t_a, 0<|r_a|<1, put c_a=-log|r_a|. Their finite-alphabet boundedness gives the same clock comparison for contraction sums. The mean contraction per word is ell times the stationary mean per letter: use expected total contraction through T_k, subtract the initial word, and compare to deterministic n_k with error at most (max c_a)E|T_k-n_k|. Hence the entropy/Lyapunov ratio is invariant under the regenerative clock whenever the stated representation and moments hold.

Equations (1)-(5) are complete calculations for the explicit hypotheses above. They do not establish the required regenerative representation for an arbitrary process, nor prove a countable-IFS dimension theorem.

## 3. Strongest actual regenerative antecedent

Comets–Fernández–Ferrari, *Processes with Long Memory: Regenerative Construction and Perfect Simulation*, arXiv:math/0009204v3, defines a_k in (2.5), beta_m=product_{j=0}^m a_j in (4.1), and requires beta=lim beta_m>0 for Corollary 4.18. It constructs a stationary renewal mark process N and mutually independent word blocks xi_l; all except the block straddling the origin are identically distributed. Theorem 4.3(iv) supplies exponential rho_k when 1-a_k decays exponentially. The original label/inequality conventions are retained in the private PDF; no off-by-one use of its tail formula is needed in (4).

Section 8 actually proves the renewal factorization by events H[j,j'] built from independent uniforms. Its identity (8.6) separates the constraints across successive renewal marks, and (8.7) factors their probabilities. Word independence is obtained using the local dependence property of Theorem 4.3(iii). Those proof operations, not only the abstract, are credited. Sections 5-6 proving all the construction and tail bounds were NOT completely read in this round; those inputs are primary antecedents with that reading limit.

For finite-alphabet exponential-tail words, H(B)<infinity and E[-log|r_B|]<infinity. Every block similarity preserves the same bounded interval as the original finite IFS, and its contraction is at most max_a|r_a|<1. The existing r26 countable-alphabet feasibility note addresses precisely the type entropy, factorial conditional supports, finite-mean windows and overshoots needed for such iid words. Its author conclusions are not adopted as an independent proof approval.

A complete Gibbs dimension theorem would still have to bind a precise Gibbs-to-chain representation, the origin-word convention, and a complete countable-family extension with exact dimensionality. This round does not silently replace those verifications with an abstract or with equations (1)-(5). Nor does it call those routine-looking remaining verifications a new substantive compatibility mechanism.

## 4. Direct finite-state alternative and its exact limits

For a stationary finite-state Markov chain S_j with s states, group b transitions into one block. Record each endpoint S_jb and all s^2 transition counts within each block. Conditional on all recorded endpoints, different block interiors are independent; conditioning additionally on each block's counts preserves that independence. The probability of a given bridge path is the product of its transition probabilities, and is identical for paths with the same counts and endpoints. Zero-probability transitions are simply absent.

For edge-labelled similarities, the counts fix the signed contraction. Recording n blocks costs at most

    (n+1)log s + n s^2 log(b+1).

Per original transition this tends to zero as b increases. Under this conditioning, translation determines the complete affine product, even with collisions. Each conditional block has at most s^(b+1) possible paths, so the source's finite sumset count has a uniform alphabet-dependent replacement. Stationarity suffices for its final sum over starts. These statements follow directly from finite conditional probabilities, and explain why finite-state dependence alone is not a fresh inverse-entropy mechanism.

However, after revealing through a segment endpoint, the tail averages to the coding law conditional on that endpoint state, not to the unconditional stationary law. A completed direct proof must supply the correct common nonsaturation control for those state laws. Replacing them by the unconditional law in Jensen would be an error. Regeneration is the stronger compatible existing reduction to inspect first. No completed Markov dimension theorem is asserted here.

## 5. Why the unrestricted ergodic route was not frozen

Jordan–Rapaport, arXiv:1908.00271v2, Theorem 1.1 and complete Section 2 were read. The proof chooses typical length-m cylinders, gives all atypical cylinders small positive weights, sets q=delta^(-1), and invokes Shmerkin's Lq formula under exponential separation. Lemma 2.3 obtains a uniform small-ball bound for all finitely many shifts of this block Bernoulli measure. Lemma 2.4 and the final cylinder count then compare the original ergodic measure to it. This is a concrete strongest compatible reduction, not a generic approximation argument.

Source148 proves Shannon dimension, not Lemma 2.3's high-q uniform bound. General ergodic dependence also need not give the source identity tau_j=(scaled finite prefix)*tau_{j+n} after a low-entropy conditioning. Neither operation was supplied here. Thus an unrestricted ergodic formula remains only an investigated direction, not a frozen feasible target or an asserted theorem. We do not promote a failure of either method into a counterexample.
