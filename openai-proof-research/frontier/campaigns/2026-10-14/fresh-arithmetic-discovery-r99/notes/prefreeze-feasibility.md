# r99 prefreeze feasibility (written before the scope freeze)

Family: 164 (Hindman finite sums and products). Pinned source proves the
positive-integer theorem by nilsequence Prediction/Alignment; its
`lem:chain-selection` (02_framework.tex) reuses Alweiss Section 5 Steps II-IV.

## Gap located

- Alweiss arXiv:2307.08901v6 Theorem 1.3: FS∪FP over Q. Its Theorem 2.4
  (integer polynomial van der Waerden scaled to Q) and the size function
  s(a/b)=max(|a|,|b|) are used to keep the shifts u and dilations k inside
  bounded-size sets. Alweiss p.2 says field versions "follow from Q" by
  compactness.
- Bowen–Sabok arXiv:2210.12290v1 Corollary 1.2 (the compactness argument
  itself, section 4.3): a first-order sentence true in Q holds only in fields
  of characteristic > p0(r). Small characteristic is not reached.
- Hunter arXiv:2308.10749v1 (exposition of Alweiss): works over Q+, and uses
  "D is finite (since N ⊂ Z has characteristic zero)" in the proof of
  Lemma 6.1. Remark 1.1 gives the C(q) != C(2q) distinctness trick.
- Kousek arXiv:2407.03304v1: char-0 density {p(x)+y,xy}; finite fields
  {x,p(x)+y,xy}; repeats that Bowen–Sabok handle "all finite fields" by
  compactness (the statement read in Bowen–Sabok is only large characteristic).
- Histories: structural r35 mixed164.md (integer read-once target, not
  characteristic p); arithmetic r94 other-screens (history exclusion);
  structural r130 other-screens: "A positive-characteristic version would need
  the whole nilsequence apparatus over function fields. That is an unbuilt
  central step." That judgement assumed the source route.

So for n >= 3 (and already for n = 2) and an infinite field of small positive
characteristic, e.g. F_2(t) or the algebraic closure of F_2, none of the read
sources supplies FS∪FP partition regularity. Search limits: two web searches
plus the above primaries; no worldwide novelty claim.

## Route and feasibility checks done before freezing

1. Replacement for integer polynomial vdW: Bergelson–Leibman Annals 150
   (math/9907201v1), Corollary 7.11: G infinite ring, P: G^n -> G^t polynomial
   over G with P(0)=0, F finite in G^n; any finite colouring of G^t has h and
   nonzero x with h + P(xF) monochromatic. Characteristic is not restricted.
   Use G = K, coordinates indexed by E, P(w0,w)_e = w_e w0^(d_e - 1) with
   d_e >= 1, F = {(1,l): l in L^E}. Then P(x(1,l)) = (l_e x^(d_e))_e.
2. Bounded parameters: replace "size <= M" by finite sets. Tychonoff
   compactness of [R]^(K^E) (K countable WLOG) gives a finite set Phi of
   (h,x) pairs working for every R-colouring. Phi is independent of the
   current variables because the colouring is pulled back to K^E along the
   linear map q -> sum q_e mu_e.
3. Update identity (checked by hand, to be checked symbolically):
   x~_j = k^(y_j) x_j (j<n), x~_n = k^(-s_U)(x_n + sum u_e mu_e),
   mu_e = x^S/x^T, y_j = 2^j, sigma_e = s_S - s_T >= 1, d_e = sigma_e + s_U:
   (x~_n + sum l_e mu_e(x~)) x~^U = (x_n + sum (u_e + l_e k^(d_e)) mu_e(x)) x^U,
   and for another U1:
   (x~_n + sum l_e mu_e(x~)) x~^(U1)
     = k^(s_U1 - s_U) (x_n + sum (u_e + l_e k^(d_e)) mu_e(x)) x^(U1).
   Lower conditions (i<n): lambda(x~_i x~^T + sum l_S x~^S)
     = lambda k^a (x_i x^T + sum l_S k^(s_S - a) x^S), a = y_i + s_T.
   All exponents are integers; negative powers of k are fine in a field.
   Positivity d_e >= 1 is needed only for P(0)=0 and holds since max S >
   max T forces s_S > s_T.
4. Nondegeneracy: isolate 0 as its own colour; x_1 is only multiplied by
   nonzero k; x_i + x_1 has the colour of x_i, so x_i != 0. Distinctness:
   char 2 gives X+X = 0 (isolated colour); odd characteristic uses a
   3-colouring psi with psi(2z) != psi(z) (multiplication by 2 is a
   fixed-point-free permutation of K^x), as in Hunter Remark 1.1.
5. Steps II-IV are characteristic-free combinatorics (Ramsey, Folkman).
6. Finite fields: compactness over the chain F_{p^(j!)} inside the algebraic
   closure gives d with the conclusion in F_{p^m} for d | m. All large m is
   NOT claimed (e.g. F_{2^m}, m prime, is not covered).

Risk recorded before freezing: the operation is a transport of Alweiss's
argument with a different recurrence input; the contribution reviewer may
judge it routine. This note does not assign any verdict.
