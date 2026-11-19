# The Jacobi symbol of the Chen–Sun determinant roots

## Abstract

We prove that the positive odd integer $c_p$ defined by Chen and Sun satisfies $(p/c_p)=1$ for every odd prime $p$. For $p\equiv1\pmod4$, a cyclic difference matrix exhibits the defining integer square, and an augmented Vandermonde determinant evaluates its character. For $p\equiv3\pmod4$, a signed Pfaffian has matching characters modulo $p$ and $4$. A doubling permutation supplies the factorial character calculation. The result, including existence and uniqueness for the defining determinant identities, is formalized in Lean 4 with Mathlib.

## Statement and prior work

The following is Conjecture 1.1 of Chen and Sun [1].

> For any odd prime $p$, the Jacobi symbol $\left(\frac{p}{c_p}\right)$ is equal to $1$.

Here $h=(p-1)/2$, $\chi(a)=(a/p)$ is the Legendre symbol, and
$$
 D_p^{(\delta)}(w)=
 \det[\chi(j^2-k^2)+w\chi(jk)]_{\delta\le j,k\le h}
 -\det[\chi(j^2-k^2)]_{\delta\le j,k\le h}.
$$
Theorem 1.1 of [1] defines $c_p$ as a positive odd integer through
$$
 D_p^{(0)}(w)=-w(hc_p)^2\quad(p\equiv1\pmod4),\qquad
 D_p^{(1)}(w)=w\left(c_p\sum_{j=1}^{h}\chi(j)\right)^2\quad(p\equiv3\pmod4).
$$
It also gives $D_p^{(0)}(w)=hD_p^{(1)}(w)$ in the first class and $D_p^{(0)}(w)=0$ in the second. Since $h>0$, the first equation at $w=1$ already determines the positive integer $c_p$, so using only the outer member of the source's chain of equalities does not change $c_p$.

Chen and Sun proved existence of these roots and posed the Jacobi conjecture after computing examples. Ren and Luo [2, Theorems 1.4–1.5] used Vandermonde factorizations to evaluate Legendre symbols of square roots associated with other determinants whose entries are powers of $i^2-j^2$ times $\chi(i^2-j^2)$, for $p\equiv1\pmod4$.

**Theorem.** For every odd prime $p$ there is a unique positive odd integer $c_p$ satisfying, for every integer $w$, the defining equation above in its prime class. For this integer, $\left(\frac{p}{c_p}\right)=1$.

Write $A_\delta=[\chi(j^2-k^2)]_{\delta\le j,k\le h}$ and $u_\delta=[\chi(j)]_{\delta\le j\le h}$ as a column. By multiplicativity, $D_p^{(\delta)}(w)=\det(A_\delta+w u_\delta u_\delta^{\mathsf T})-\det(A_\delta)$. We use the same $\chi$ for the character of $\mathbb F_p$.

## Preliminary facts

The points $x_j=j^2$ for $0\le j\le h$ are distinct in $\mathbb F_p$. If $j^2=k^2$, then $j=k$ or $j+k=0$ in the field, and $0\le j+k\le p-1$. The positive indices $1,\ldots,h$ represent the pairs $\{a,-a\}$ of nonzero residues once each. Thus the points $x_1,\ldots,x_h$ enumerate the nonzero squares. The off-diagonal entries of each $A_\delta$ are $\pm1$, and its diagonal is zero. If this entry pattern occurs in even size, its determinant is odd. Modulo $2$ the matrix is $I+J$, where the all-ones matrix $J$ satisfies $J^2=0$, so $(I+J)^2=I$.

For $a=j^2\ne0$ the equation $z^2=t^2-a$ has $p-1$ solutions $(t,z)$. The change of variables $(t,z)\mapsto(t-z,t+z)$ is invertible since $p$ is odd, and its image on the solutions consists of pairs with product $a$. Counting by $t$ gives $p+\sum_t\chi(t^2-a)$, so $\sum_t\chi(a-t^2)=-\chi(-1)$. Removing the $t=0$ term $1$ and grouping $t,-t$ gives row sum $-1$ of $A_1$ when $p\equiv1\pmod4$ and zero when $p\equiv3\pmod4$.

We use cyclicity of $\mathbb F_p^\times$, Euler's criterion, and the classical laws of quadratic reciprocity. Euler's criterion $\chi(a)=a^h$ in $\mathbb F_p$ follows by writing nonzero $a$ as a power of a generator, whose $h$-th power is $-1$. Wilson's identity follows by pairing inverses, with the only self-inverse elements $1,-1$. Stripping the last $t$ factors of $(p-1)!$ gives
$$
 (p-1-t)!\,t!=(-1)^{t+1}\qquad (0\le t\le p-1)
 \tag{1}
$$
in the field. In particular every factorial with argument less than $p$ is a unit. The supplement for $2$ gives $\chi(2)=1,-1,-1,1$ in the classes $1,3,5,7$ modulo $8$, respectively.

## The integer square for $p\equiv1\pmod4$

Let $p=4m+1$, so $h=2m>0$. Choose a generator $g$ of $\mathbb F_p^\times$ and order the positive indices by their squares $g^{2i}$, $0\le i<h$. In this order $A=A_1$ has entries $\chi(g^{2(i-j)}-1)$ because the factor $g^{2j}$ is a nonzero square. Also $u=u_1$ has entries $(-1)^i$, since the representative is $\pm g^i$, $g$ is a nonsquare and $\chi(-1)=1$. The same value of $\chi(-1)$ makes $A$ symmetric.

On indices modulo $h$ let $S_{ij}=[i=j-1]-[i=j+1]$, with brackets denoting indicators. Let $I_0=\{0,\ldots,h-3\}$, empty for $h=2$, and $N=(AS)_{I_0,I_0}$. For $h=2$ the matrix $S$ is zero, $N$ is empty with determinant $1$, and $Q=R=I_2$ below. Two circulant matrices with entries $a(i-j)$ and $s(i-j)$ commute: the product entry is $\sum_t a(t)s(i-j-t)$, which is symmetric in the two functions by substitution. Hence $AS$ is skew-symmetric because $S^{\mathsf T}=-S$ and $A^{\mathsf T}=A$. The leading submatrix $S_{I_0,I_0}$ has $1$ on the superdiagonal and $-1$ on the subdiagonal. Its determinant is $1$. Expansion along the first row and then the first column deletes the first two indices with coefficient $(-1)\cdot1\cdot(-1)=1$, and the empty determinant is $1$.

Let $L$ have as its two rows the indicators of even and odd indices. Then $LS=0$ since $j-1,j+1$ have equal parity even at the wraparound, and also $u^{\mathsf T}S=\mathbf1^{\mathsf T}S=0$. The last two columns of $L$ form $I_2$, $L\mathbf1=(m,m)^{\mathsf T}$, and $Lu=(m,-m)^{\mathsf T}$. Put $P(w)=A+wuu^{\mathsf T}$. Define $Q$ by using the first $h-2$ columns of $S$ followed by the two corresponding final standard basis vectors. Define $R$ by using the first $h-2$ standard basis rows followed by the rows of $L$. Both matrices are block lower triangular with determinant $1$, using the path determinant for $Q$. The top left block of $RP(w)Q$ is $N$, since $P(w)S=AS$. Its lower left block vanishes because $LAS=LSA=0$. The last block is $K(w)=K(0)+wm\bigl(\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\bigr)$, by $Lu$ and the two final entries of $u$. At $w=0$ this proves $\det N\mid\det A$ over $\mathbb Z$.

The source index-zero row and column have off-diagonal entries $1$, because the other indices are nonzero and $\chi(-1)=1$. The perturbation at that index vanishes. Place the index last and extend $R,Q$ by the identity there. The leading block is still $N$ with zero below it, using $\mathbf1^{\mathsf T}S=0$. The last block is
$$
 \begin{pmatrix}
 K_{00}(w)&K_{01}(w)&m\\ K_{10}(w)&K_{11}(w)&m\\ 1&1&0
 \end{pmatrix}.
$$
For the upper left block $\bigl(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\bigr)$ its determinant is $m(b+c-a-d)$, so its change is $-4wm^2$. Thus
$$
 D_p^{(0)}(w)=-w h^2\det N . \tag{2}
$$
The Pfaffian identity proved below gives $\det N=f_0^2$ for an integer $f_0$, as $N$ is skew and of even size. Since $\det N$ divides the odd determinant of $A$, $f_0$ is odd and nonzero. This gives $c_p=|f_0|$, uniquely by $w=1$ and $h>0$.

## The character for $p\equiv1\pmod4$

In $\mathbb F_p$ use the source order and let $V=(x_j^i)_{0\le j,i\le h}$ with determinant $\Delta$. Euler's criterion gives $u_0(j)=x_j^m$ since $h=2m$ and $m\ge1$. Expanding $(x_j-x_k)^h$ gives $A_0=VCV^{\mathsf T}$ with reversal diagonal entries $(-1)^i\binom hi$ at column $i$. The perturbation adds only $w$ to $C_{mm}$. The reversal has $m$ transpositions, and the two weights for $i,h-i$ outside the middle index have product $\binom hi^2$ since $h$ is even. For $B=\prod_{i=0}^{m-1}\binom hi$ this gives $D_p^{(0)}(w)=w(-1)^m(B\Delta)^2$ in the field. Comparing at $w=1$ with (2) and $2h=-1$ in the field,
$$
 c_p^2=(-1)^{m+1}(2B\Delta)^2. \tag{3}
$$

The Vandermonde formula $\det(v_j^i)=\prod_{j<k}(v_k-v_j)$ follows by induction in the polynomial ring of the points. In the last point the determinant vanishes at each earlier point by row equality, and expansion along its row gives the smaller Vandermonde determinant as leading coefficient. Dividing by the distinct monic linear factors over the polynomial domain proves the formula and permits specialization. For our points the factors with larger index $k$ multiply to $\prod_{j=0}^{k-1}(k^2-j^2)=k!(k(k+1)\cdots(2k-1))=k(2k-1)!$. It follows that $\Delta=h!\prod_{k=1}^h(2k-1)!$. The odd indices $t=1,3,\ldots,2h-1$ pair without fixed points with $p-1-t$, since $h$ is even, and each factorial pair multiplies to $1$ by (1). Thus $\Delta=h!$. Also $(h!)^2=-1$ by (1), so Euler's criterion gives $\chi(h!)=(-1)^m=\chi(2)$, by the supplement for $p=4m+1$.

Write $M=\chi(m!)$, $H=\chi(h!)$, $E=\chi(2)$, $O=\prod_{i=0}^{m-1}\chi(2i+1)$. These are signs since all arguments are units. Splitting $h!$ into even and odd factors gives $H=E^m M O$. Pairing $(2i)!,(2i+1)!$ for $0\le i<m$ gives $\prod_{i=0}^{h-1}\chi(i!)=O$, since each repeated factorial has squared character $1$. The denominators in the factorial formulas for $B$ use each $i!$ for $0\le i\le h$ except $m!$, giving $\chi(B)OH=H^m M$. Substitute $H=E^m MO$ on the left and $H=E$ on the right. Cancelling $E^m M$ gives $\chi(B)=1$. Thus $U=2B\Delta$ satisfies $\chi(U)=1$. Raising (3) to the $m$-th power gives $c_p^h=U^h=1$ since $m(m+1)$ is even. Consequently $\chi(c_p)=1$ by Euler's criterion. Jacobi reciprocity for positive odd $c_p$ and $p\equiv1\pmod4$ gives $(p/c_p)=(c_p/p)=1$.

## Pfaffian identities and the sign modulo four

For a skew-symmetric $2m$-by-$2m$ matrix $A$, its Pfaffian is a sum over perfect matchings of the indices. In each pair $(i,j)$ take $i<j$, contribute $A_{ij}$, and multiply by the sign of the permutation listing the pairs consecutively. Interchanging two pairs preserves the sign. Grouping by the partner $j>0$ of index zero gives coefficient $(-1)^{j-1}A_{0j}$ times the Pfaffian with the pair deleted, because $j$ moves past $j-1$ slots. The empty value is $1$. The recursion uses only addition and multiplication with integer coefficients.

Over a field of characteristic zero or $>2m$, multiply the Pfaffian by $2^m m!$ to obtain the full permutation sum with summand $\operatorname{sgn}(\sigma)\prod_{i=0}^{m-1}A_{\sigma(2i),\sigma(2i+1)}$. The leading factor counts the orders and orientations of each matching, all with equal signed contribution because reversing an entry of a skew pair changes both signs. On $BAB^{\mathsf T}$ this full sum is multilinear in the rows of $B$, since each row occurs in exactly one bilinear pairing per term. With repeated rows the terms cancel in pairs by transposition of their labels, so the form is alternating. Expanding the rows in the standard basis leaves only families of distinct basis vectors, each contributing its permutation sign times the value at the standard basis. The signed sum of scalar coefficients is $\det B$. Cancel the unit $2^m m!$ to obtain
$$
 \operatorname{Pf}(BAB^{\mathsf T})=\det(B)\operatorname{Pf}(A). \tag{4}
$$

To prove $\operatorname{Pf}(A)^2=\det A$ over $\mathbb Z$, work over $\mathbb Q$. Both sides equal $1$ in size zero. If the first row is zero, both sides vanish. Otherwise permute indices to put a nonzero entry $a$ in position $(0,1)$, preserving the square by (4). The first block is $J=\bigl(\begin{smallmatrix}0&a\\-a&0\end{smallmatrix}\bigr)$, and with block form $A=\bigl(\begin{smallmatrix}J&B\\ C&D\end{smallmatrix}\bigr)$ we have $C=-B^{\mathsf T}$. Direct multiplication with $E=\bigl(\begin{smallmatrix}I&0\\-CJ^{-1}&I\end{smallmatrix}\bigr)$ gives $EAE^{\mathsf T}=\operatorname{diag}(J,D-CJ^{-1}B)$, using $(J^{-1})^{\mathsf T}=-J^{-1}$. The second block is skew. The basis change has determinant $1$. Pfaffian expansion multiplies the smaller Pfaffian by $a$, and the block determinant multiplies the smaller determinant by $a^2$. Induction proves the identity over $\mathbb Q$. Injectivity of the integer embedding gives the integer identity.

For even size and upper entries $\pm1$, the Pfaffian with all upper entries $+1$ is $1$, by induction and the alternating sum of $2m-1$ ones. Every even principal submatrix has odd Pfaffian by reduction of its upper entries to $1$ modulo $2$. Starting with all upper entries $+1$, flip each upper sign needed to obtain $A$. The coefficient of a flipped entry in the matching sum is the Pfaffian of the deleted-pair submatrix up to a sign independent of the remaining matching, obtained by moving the pair to the front. This coefficient is odd, so each flip changes the residue by $2$ modulo $4$. It follows that
$$
 f=\operatorname{Pf}(A)\equiv\prod_{i<j}A_{ij}\pmod4,\qquad
 \chi_4(f)=\prod_{i<j} A_{ij}, \tag{5}
$$
where $\chi_4$ takes values $1,-1,0$ on the residue classes $1,3,\text{even}$, respectively.

## The odd-class root and character

For $p=3$ the one-entry determinant difference $D_3^{(1)}(w)$ is $w$ and the half-range character sum is $1$. Thus $c_3=1$ and the symbol is $1$. Now let $p=4m+3>3$ so $m\ge1$ and $h=2m+1$. The matrix $A_1$ is skew since $\chi(-1)=-1$. Its row sums vanish by the preliminary count, and its column sums vanish by skew-symmetry. The minor $A_2$ has even size and odd determinant. Put $f=\operatorname{Pf}(A_2)$. The rank of $A_1$ over $\mathbb Q$ is $h-1$ by this nonzero minor and the zero row sums. Both kernels are spanned by $\mathbf1$. The adjugate identities then force every row and column of $\operatorname{adj} A_1$ to be constant, and its first diagonal entry is $\det A_2=f^2$. In the rank-one determinant expansion any term selecting two or more perturbed columns vanishes by proportionality. Expanding the single changed columns by their cofactors gives
$$
 D_p^{(1)}(w)=w f^2\left(\sum_{j=1}^h\chi(j)\right)^2.
$$
The sum is odd since it contains an odd number of signs. Therefore $c_p=|f|$ exists and is unique by evaluation at $w=1$. Jacobi reciprocity gives $(p/c_p)=\chi(c_p)\chi_4(c_p)$, also valid if $p\mid c_p$ because both sides vanish. The product of these characters is invariant under negation since $\chi(-1)=\chi_4(-1)=-1$. It is enough to show $\chi(f)=\chi_4(f)$.

Modulo $p$, on the indices $2,\ldots,h$, let $V=(x_j^i)_{0\le i<2m}$, $X=\operatorname{diag}(x_j)$, $W=XV$, and label the columns of $W$ by the exponents $1,\ldots,2m$, so that column $e$ of $W$ is $(x_j^{e})_j$. By $x_j^h=1$ and oddness of $h$ the endpoint terms in $(x_j-x_k)^h$ cancel. The other terms give $A_2=W C W^{\mathsf T}$, where $C$ is indexed by the same labels $1,\ldots,2m$, with $C_{i,h-i}=(-1)^{h-i}\binom hi$ for $1\le i<h$ and zeros elsewhere. It is skew because $h$ is odd and $\binom hi=\binom h{h-i}$. The only nonzero matching lists $1,h-1,2,h-2,\ldots,m,m+1$ and has positive sign because each high entry has $2(m-i)$ later entries below it. Write $B_o=\prod_{i=1}^m\binom hi$ and $s=\sum_{i=0}^{m-1}i$. As $h-i\equiv i-1\pmod2$ and $\chi(-1)=-1$, $\chi(\operatorname{Pf}(C))=(-1)^s\chi(B_o)$. Since $p>2m$, (4) applies, and the diagonal factors $x_j$ are nonzero squares. Reduction commutes with the Pfaffian by its integer recursion. We get
$$
 \chi(f)=\chi(\det V)(-1)^s\chi(B_o). \tag{6}
$$
By (5) and the Vandermonde formula, $\chi_4(f)=\prod_{j<k}\chi(x_j-x_k)=\chi(\det V(-x))$. Negating the points scales column $i$ by $(-1)^i$. Pairing adjacent columns gives factor $(-1)^m$, so
$$
 \chi_4(f)=(-1)^m\chi(\det V). \tag{7}
$$
The Vandermonde determinant is nonzero by distinctness, and the binomial coefficients are nonzero by their factorial formulas with $h<p$.

Write $F(a)=\chi(a!)$ for $a<p$. The denominator indices $i,h-i$ in $B_o$ run once through $1,\ldots,2m$, so $\chi(B_o)\prod_{a=1}^{2m}F(a)=F(h)^m$. Pairing $F(2t)F(2t+1)$ gives $O=\prod_{t=0}^{m-1}\chi(2t+1)$ for the product from $0$ through $2m-1$. Splitting $(2m)!$ into even and odd factors gives $F(2m)=\chi(2)^m F(m)O$. Here $\chi(2)^m=1$ since either $m$ is even or $p\equiv7\pmod8$ and $\chi(2)=1$. As $O^2=F(0)=1$, the product $\prod_{a=1}^{2m}F(a)=O\,F(2m)$ equals $F(m)$, and therefore
$$
 \chi(B_o)F(m)=F(h)^m. \tag{8}
$$

Doubling $a$ and taking the positive representative of its pair up to sign permutes $1,\ldots,h$, since multiplication by $2$ is invertible and commutes with negation. The representative is $2a$ for $a\le m$ and $p-2a$ for $a>m$. With $S_1,S_2$ the character sums over those two intervals, invariance under the permutation and $\chi(-1)=-1$ give $S_1+S_2=\chi(2)(S_1-S_2)$ over $\mathbb Z$.

If $m=2r$, then $p\equiv3\pmod8$ gives $\chi(2)=-1$ and $S_1=0$. Exactly $r$ of the $2r$ signs in the first interval are negative, so $F(m)=(-1)^r$ and (8) gives $\chi(B_o)=(-1)^r$. If $m=2r+1$, then $p\equiv7\pmod8$ gives $\chi(2)=1$ and $S_2=0$. Exactly $r+1$ of the $2r+2$ signs in the second interval are negative, giving $F(h)=F(m)(-1)^{r+1}$. Now (8) gives $\chi(B_o)=(-1)^{r+1}$. Since $m+s=m(m+1)/2$ has the parity of $r$ and $r+1$ in the two respective cases, we have $\chi(B_o)=(-1)^{m+s}$. Equations (6) and (7) yield $\chi(f)=\chi_4(f)$, and reciprocity completes the proof.

## Small primes

The values below were computed from the defining integer coefficients by fraction-free elimination and checked by the Jacobi algorithm. The universal proof does not use these computations.

| $p$ | $c_p$ | $(p/c_p)$ |
|---:|---:|---:|
| 3 | 1 | 1 |
| 5 | 1 | 1 |
| 7 | 1 | 1 |
| 11 | 1 | 1 |
| 13 | 3 | 1 |
| 17 | 21 | 1 |
| 19 | 17 | 1 |
| 23 | 1 | 1 |
| 29 | 83 | 1 |
| 31 | 33 | 1 |
| 37 | 9095 | 1 |
| 41 | 98835 | 1 |
| 43 | 67119 | 1 |
| 47 | 1870591 | 1 |
| 53 | 4689023 | 1 |

## Correspondence with Lean

All declaration names in the table are in the `ChenSun` namespace. The declarations `positiveMatrix_det_odd_even_class` and `det_entry_zero_border` are private to `ChenSunEvenExistence.lean`.

| Step | Lean declarations and route |
|---|---|
| Definitions and recovery | `entryMatrix`, `D`, `halfSum`, `IsCp`, `cp`, `cp_eq_of_spec`, `cp_unique`. Lean defines cp by the natural square root of the quotient at $w=1$ and certifies the positive root by IsCp. |
| Preliminary facts | `point_injective`, `positiveMatrix_det_odd_even_class`, `positiveMinor_det_odd`, `positiveMatrix_row_sum`. Lean derives the row sum by expanding powers over the finite field and lifting with integer bounds. The text counts solutions to a quadratic equation. |
| Even-class integer square | `square_circulant_order`, `cyclicDifference_skew`, `det_cyclicDifference_castAdd`, `even_block_coefficient`, `even_circulant_coefficient`, `det_entry_zero_border`, `cp_exists_one_mod_four`, `even_root_exists`. Lean applies its preceding skew_det_isSquare_int, proved by rational block elimination and descent of the square. The text applies the signed Pfaffian determinant identity. |
| Even-class character | `entryMatrix_mod_even`, `det_sub_perturbed`, `D_mod_even_square`, `cp_square_mod_even`, `det_square_vandermonde`, `factorial_reflection`, `vandermonde_eq_half_factorial`, `binomialProduct_character`, `cp_legendre_even`, `chen_sun_one_mod_four`. Lean takes the Vandermonde formula from Mathlib's `Matrix.det_vandermonde`, and Euler's criterion, Wilson's theorem and Jacobi reciprocity from Mathlib. The text sketches proofs of these classical facts. |
| Pfaffian identities | `pfaffian`, `pfPermutation_eq`, `pfPermutation_congruence`, `pfaffian_congruence`, `pfaffian_sq_rat`, `pfaffian_sq_int`, `sourcePfaffian_sq`. Lean partitions the permutation sum by the position of zero to prove normalization and uses Mathlib alternatization and the basis determinant for (4). The text counts arrangements of a matching and expands rows in the basis. |
| Modulo four | `int_pfaffian_mod_four`, `upper_sign_product`. Lean proves the single-flip property by induction using the recursive expansion. The text reads the coefficient from the matching sum. |
| Odd-class defining equation | `D_odd_minor`, `cp_exists_three_mod_four`, `cp_square_eq_minor`, `cp_three_spec`, `chen_sun_three`, `odd_jacobi_iff_minor_root`. Lean uses determinant row and column operations over $\mathbb Q$ for the perturbation, and the text identifies the adjugate through its two kernels. |
| Odd-class character | `odd_minor_mod_factorization`, `oddWeights_skew`, `pfaffian_antidiagonal`, `oddWeights_pfaffian_character`, `upper_sign_vandermonde`, `doubling_balance`, `product_of_balanced_signs`, `odd_binomial_character`, `odd_signed_root`. Both the text and final Lean proof use (8) directly. The standalone theorem even_factorial_product_character formalizes the separate even-factorial evaluation in the supplied proof's alternative odd-class argument. |
| Full endpoint | `conjecture_iff_odd_signed_root`, `conjecture_with_root_iff`, `chen_sun_conjecture`, `chen_sun_conjecture_with_root`, `jacobi_cp_eq_one`. |

## Limits

The theorem treats the conjectured Jacobi symbol and the two equations defining the positive odd root. Two prior-art reviews located related Legendre-symbol evaluations and found no resolution of Conjecture 1.1. As of 18 November 2026, arXiv lists only version 1 of [1], with no journal reference. The Semantic Scholar and OpenAlex citation services list no citing works, and ProbXiv lists the problem as open. arXiv keyword search and Google Scholar were not used, because their robots files disallow automated access, and some 2026 journal papers on related determinants were read only through their reference lists. The prior-art claim is limited to these searches.

## References

1. Deyi Chen and Zhi-Wei Sun, *On determinants involving $\left(\frac{j^2-k^2}{p}\right)$ and $\left(\frac{jk}{p}\right)$*, arXiv:2408.14401v1, 26 August 2024. [Preprint](https://arxiv.org/abs/2408.14401v1)
2. Chen-Kai Ren and Xin-Qi Luo, *On certain determinants and the square roots of some determinants involving Legendre symbols*, arXiv:2407.04556v2, 12 July 2024. [Preprint](https://arxiv.org/abs/2407.04556v2)
