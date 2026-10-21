# Integrated height calculation — PREFREEZE, no nominee

This is a paid exploratory reduction, not a frozen author-proof submission, independent verdict, contribution grade or claim of priority. It was investigated only after reading the complete pinned determinant, interpolation, parameter and series files, and relevant original project scopes. The exact scalar source is stipulated true. No geometry is audited. The purpose is to identify what its strongest composition already pays before claiming an additional operation.

## 1. Operative contracts, not only the headline

Use Source017's labels geom:interpolation, det:matrix, det:row-count, det:translation, det:collision and det:comparison. The interpolation map has domain monomials with w0*h+sum(w_i*alpha_i)<=H and rows (j,s,beta) with 0<=j<K and v0*s+sum(w_i*beta_i)/theta<H. Its two strict conditions are K*theta^m<1 and K*(w0/v0)*theta^m<1. Successive thresholds for w_i are independent of all center locations; the sufficiently divisible H threshold may depend on all fixed centers. Coordinates need only be pairwise distinct as j varies for each fixed i. No independence of the fields or coordinates is required.

The source obtains M ~ K theta^m H^(m+1)/((m+1)! v0 prod w_i), bbar=(MH)^(-1) sum_rows w beta <= theta. At one fixed complex embedding, translation and collision bound each term by error powers exp(-nu sum_rows w(a-beta)) and exp(-c sum_a n_a^2), c=log(2)/4. Their combined error is

E_an = nu/F0 + 2 log(2)/v0 + 100K/w0
       + [log(4)+log(2K)+nu+log(200K)]/w*,

where F0>2/theta, T_i=ceil(F0 w_i/v0), G_i=sum_{1<=k<T_i}(-1)^(k+1)t^k/k. The high-order tail budget is essential: a surviving product of d_i tails satisfies sum d_i w_i < H/F0. This is not an arbitrary change-of-center result.

The collision result applies to the entire row-vector expansion, with column-independent coefficients, uniformly in every row-term choice and chosen full-row minor. The analytic exponent after division by MH is

E_an+o(1)+max(-c L_H, -nu[A(1-eta)-bbar]),
L_H -> L=eta^2 K theta^m/((m+1)v0 A^m).

## 2. Fixed field and height normalization

Fix a number field F with a specified embedding F -> R; write d=[F:Q]. This does not require F totally real. Work inside the compositum E=F(i) at the resulting complex embedding. Since i is not in this real copy of F, [E:Q]=2d; the selected complex place has local degree 2.

Normalize absolute values by the usual real/complex modulus, |p|_p=p^(-1), local degrees n_v, and sum_v n_v log|a|_v=0. Define

h(x)=[E:Q]^(-1) sum_v n_v log max(1,|x|_v), H_abs(x)=exp h(x).

These heights are independent of E. For a rational reduced p/q, H_abs=max(|p|,|q|), not just q. Near pi they are comparable. No naive polynomial-height convention is silently substituted.

To test the integrated reduction, suppose a sequence x in F has unbounded h(x) and satisfies |x-pi|<=exp(-nu h(x)). Set w_i=ceil h(x_i) successively and r_i=2i*x_i. The w_i are positive integers and can meet the center-independent thresholds. Eventually x_i is nonzero, so c_{ji}=j r_i meets every distinctness requirement. Source interpolation selects a nonzero full-row minor at these centers. The source translation proof remains literally applicable because |j(r_i-2pi i)| <= 2K exp(nu) exp(-nu w_i). All limits in H occur after F, m, weights and x_i have been fixed.

## 3. Row subtraction survives the norm operation

Regard that selected minor before evaluation as a polynomial Delta(Z_1,...,Z_m) over Q(i), replacing r_i by 2i Z_i in the matrix. For a column exponent alpha and a row beta, its entry vanishes unless alpha>=beta coordinatewise. Every surviving entry has degree at most alpha_i-beta_i in Z_i. Consequently, in every determinant permutation,

D_i = sum_selected_columns alpha_i - sum_all_rows beta_i

is a common upper bound for the separate Z_i degree. If any D_i<0, every permutation term vanishes, contradicting nonvanishing at x. Thus all D_i>=0. The full-simplex column budget gives

sum_i w_i D_i <= MH - sum_rows w beta = MH(1-bbar).

This is stronger than bounding every entry by its column degree and forgetting beta. We do not infer D_i from the total degree or assume a homogeneous determinant; only separate degree bounds are used.

Put L_i=lcm(1,...,T_i-1), with empty lcm=1, and D_H=prod_i L_i^floor(H/w_i). Then

P(Z)=D_H^M Delta(Z) is in Z[i][Z_1,...,Z_m].

Each entry's logarithmic-polynomial denominator divides D_H. The scalar D_H^M therefore clears the entire determinant. The source elementary lcm estimate, Lambda=4log(2), gives

log D_H/H <= Lambda [F0 m/v0 + sum_i 1/w_i].

Coefficient length is also paid. In the coefficient l1 norm in Z, use |t|=1/2, where sum_{k<T_i}|t|^k/k<=log(2), and |1+t|^h<=2^h. Cauchy's coefficient bound, binomial(alpha,beta)<=2^|alpha|, and 2K+log(2)<=3K give

length(entry) <= 2^(s+h) (6K)^|alpha|.

Permutation expansion thus yields

length(Delta) <= M! exp(MH E_coef),
E_coef=log(2)/w0 + log(2)/v0 + log(6K)/w*.

This is a coefficient bound at every embedding, not a supposition that conjugate approximation errors are small.

## 4. Product formula with the selected complex place removed

For nonzero P(x), finite places satisfy

|P(x)|_v <= prod_i max(1,|x_i|_v)^D_i,

because Gaussian integers are integral everywhere. Every other archimedean place satisfies the same bound with coefficient factor length(P). Conjugating i preserves the absolute coefficient lengths. Multiply these inequalities over all places except the selected complex place, and use the product formula. Its local degree is 2, so

log|P(x)| >= -(d-1)log length(P) - d sum_i D_i h(x_i).

More exactly, a nonnegative selected-place term sum_i D_i log max(1,|x_i|) can be retained; discarding it is harmless. There is no loss of 2 from adjoining i. This proves the needed inequality directly; primary Liouville lemmas are comparison antecedents, not a gap in this calculation.

Since h(x_i)<=w_i, D_i>=0, and P=D_H^M Delta,

log|Delta(x)|/(MH) >= -d(1-bbar) - E_ar,F - o(1),
E_ar,F = d Lambda [F0 m/v0+sum_i 1/w_i] + (d-1)E_coef.

Here o(1)=(d-1)log(M!)/(MH)->0 for fixed m and weights. Notice that applying a norm only after bounding entries would lose the useful beta subtraction. Carrying the polynomial through the product formula keeps it, using a classical separate-degree Liouville inequality.

## 5. Close the strongest fixed-field comparison

The source two-case argument now has exact margins

g_d=nu[A(1-eta)-theta]-d(1-theta)>0,
E_ar,F+E_an<g_d,
cL>d+E_ar,F+E_an.

If nu>2d, use par:constants with nu/d in place of nu to obtain rational theta,A,B,C with theta<A<B<1, A^2<theta, C>1, B<1/C, B<Ctheta<1. Choose eta small enough that g_d>0. Fix a small positive tolerance below min(g_d/2,1/2), and first choose F0 large to suppress nu/F0.

Next let K=floor(C^m), w0=B^(-m), v0=2K theta^m w0. The exact source volume conditions remain true. As m grows,

K/w0 ->0, m/v0 ->0, 1/w0 ->0,
L=eta^2(B/A)^m/[2(m+1)] -> infinity.

The field degree d is fixed throughout these limits. It follows that one finite m makes all w_i-independent errors small and cL>d+1. Finally choose the x_i successively with arbitrarily large heights, making sum_i 1/w_i and all remaining 1/w* errors small while satisfying interpolation thresholds. Then choose H sufficiently large and divisible. The lower and upper determinant bounds contradict one another. Thus the proposed fixed-field exceptional sequence with nu>2d is excluded by this source/classical composition.

If phrased as a working consequence, this yields a height threshold depending on F and nu, above which all x in the specified real copy of F obey |pi-x|>H_abs(x)^(-nu). The calculation supplies no effective threshold. Bounded-height finiteness can be seen without an additional theorem: degree<=d and bounded absolute height imply bounded coefficients of the primitive minimal polynomial, by the elementary symmetric-polynomial bound <=2^d H_abs^d. No equality statement for a generalized exponent, Minkowski lower approximation theorem, endpoint nu=2d, varying-field statement, or comparison at naive polynomial height is asserted here.

## 6. Why this is not the requested substantial nominee

The geometric rank theorem, full-simplex volume and analytic collision gain are precisely the stipulated source operations. Polynomial separate-degree subtraction is determinant bookkeeping. The number-field arithmetic replacement is the classical product formula / Liouville inequality, not a new height theorem. Waldschmidt's 1980 Lemma 2.2 explicitly displays this separate-degree height cost and cites Mignotte–Waldschmidt's earlier Lemma 3. Laurent's 2000 Theorem 1 supplies the preexisting Taylor-degree determinant mechanism used by Source017.

The integrated calculation matters because declaring the field extension unproved merely because rational denominator clearing no longer applies would be wrong. It pays that extension. It does not isolate a substantial operation left after the strongest composition. Accordingly no full author-proof nominee is frozen or submitted. No independent correctness or contribution grade is assigned, and no old source-derived scope is renamed.
