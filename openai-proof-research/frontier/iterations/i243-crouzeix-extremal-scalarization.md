# I243 — extremal complete scalarization

**Verdict: a complete proof of four-dimensional equality scalarization is supplied.** Under the stipulated pinned complete theorem and the named external scalar-tuple input,

\[
 A\in M_4(\mathbb C),\qquad \psi_{\rm cb}(A)=2
 \quad\Longrightarrow\quad \psi(A)=2.
\]

Consequently the numerical range is a nondegenerate disk, by the existing scalar rigidity theorem. The result does not assume a polynomial extremizer, a degree bound, a Jordan condition, smoothness of the numerical-range boundary, or a lower inradius. The requested attained quadratic problem also has a degree-preserving scalar witness. The proof does not give a reducing nilpotent block in the matrix-valued output.

This is a candidate substantial finding for independent parent review; the supplied accepted count remains **nine**. No shared ledger, staging, commit, publication or acceptance record was changed. The scalar classification itself and the auxiliary quadratic-column lemma are not separately nominated.

## Exact statements

Let

\[
 \psi_K(B)=\sup_{0\ne p\in\mathbb C[z]}
 \frac{\|p(B)\|}{\max_K|p|},\qquad
 \psi_{{\rm cb},K}(B)=\sup_{m\ge1,\,P\ne0}
 \frac{\|P[B]\|}{\max_K\|P\|},
\]

where \(W(B)\subset K\), denominators are nonzero, \(P\) ranges over finite matrix polynomials, and \(P[B]=\sum B^j\otimes P_j\). Put \(\psi(B)=\psi_{W(B)}(B)\), and similarly for \(\psi_{\rm cb}\).

**Theorem 4.** For every \(A\in M_4(\mathbb C)\),

\[
 \psi_{\rm cb}(A)=2\quad\Longleftrightarrow\quad\psi(A)=2.
\]

Hence \(\psi_{\rm cb}(A)=2\) implies \(W(A)=a+\rho\overline{\mathbb D}\) for some \(a\in\mathbb C\), \(\rho>0\).

**Theorem 4Q.** For every \(A\in M_4(\mathbb C)\), every positive integer \(m\), and every \(P\in M_m(\mathbb C)[z]\) of degree at most two, if

\[
 \max_{W(A)}\|P\|=1,\qquad\|P[A]\|=2,
\]

then there is a scalar polynomial \(p\) of degree at most two with

\[
 \max_{W(A)}|p|=1,\qquad\|p(A)\|=2.
\]

The existing ACV scalar classification then gives

\[
 p(z)=c(z-a)^k,\qquad
 A\simeq_u aI+\rho(C_k\oplus B),\qquad
 k\in\{1,2\},\quad c\ne0,\quad\rho>0,\quad w(B)\le1.
\]

Here \(C_1\) is the norm-two nilpotent block and \(C_2\) is the three-dimensional Crabb matrix with both superdiagonal entries \(\sqrt2\). This classification is credited to ACV, not claimed as new.

For every fixed \(0<r\le1\), the question's additional hypotheses \(r\overline{\mathbb D}\subset W(A)\) and minimum enclosing disk \(\overline{\mathbb D}\) therefore give \(W(A)=\overline{\mathbb D}\) at exact complete equality. No quantitative modulus is asserted.

The fully expanded proof is in [analytic-attempt.md](../experiments/i243_crouzeix_extremal_scalarization/analytic-attempt.md), beginning at “Completed proof.” It contains the quotient-lift construction, exact residual, uniform exterior estimate, nonsmooth-domain limit, pencil classification, and both final arguments.

## What ACV actually proves, and the new step

ACV's primary Sections 2, 5 and 7 were read in full. Its finite-dimensional quotient norm is attained at a rectangular level \(s\times r\) with \(r+s\le n\). A minimal norming pair has full Schmidt ranks \(r,s\), and its two base Schmidt spaces are orthogonal. In dimension three the only nonscalar possibilities are a column or row. Scalar-tuple square-function equality kills products on a cyclic input; the monogenic algebra then contradicts a genuinely two-dimensional output. In dimension four this argument leaves \((r,s)=(2,2)\), as well as larger possible cyclic square-zero ideals in columns.

The new route uses the **positive-block slack in the pinned direct proof**. It does not amplify ACV's scalar output-rigidity theorem. A vanishing slack forces a rank bound on a compression of the original matrix's positive resolvent. That is incompatible with a simple supporting eigenvalue whenever a norming pair has more than one Schmidt vector on either side. In dimension four, repeated supporting eigenvalues in every direction force a repeated two-dimensional block by an elementary Hermitian-pencil calculation.

## Proof of the main new implication

The complete bound and \(\psi\le\psi_{\rm cb}\) give the easy direction. Assume \(\psi_{\rm cb}(A)=2\).

**1. Preserve the original domain when removing boundary eigenvalues.** A boundary eigenvector is reducing: positivity of a supporting Hermitian slack makes it an adjoint eigenvector too. Removing these scalar summands leaves \(A_0\) of size at most three and a diagonal block whose calculus on the original \(K=W(A)\) has norm at most one. Thus \(\psi_{{\rm cb},K}(A_0)=2\). The ACV column argument extends to this same \(K\): on a cyclic module, square-zero elements form an ideal of dimension

\[
 \sum_\lambda\lfloor r_\lambda/2\rfloor\le1
\]

when the base has size at most three. Norming column outputs are collinear, so a scalar linear combination has norm two and quotient norm at most one on \(K\). Hence \(\psi_K(A_0)=2\), and \(\psi(A)=2\). This avoids the incorrect inference that a scalar extremizer on a smaller numerical range is automatically bounded on the original one.

**2. Work with a fixed norming pair even without polynomial attainment.** We may now suppose \(\sigma(A)\subset\operatorname{int}K\). ACV's quotient extremal supplies \(X\in M_{4,r}\), \(Y\in M_{4,s}\), each of Hilbert–Schmidt norm one, with full column ranks, \(X^*Y=0\), and \(r+s\le4\). If \(r=s=1\), it is already scalar. Otherwise \(\max(r,s)>1\).

A quotient element of norm one has polynomial lifts \(F_j\) with the **same exact matrix evaluation** and \(\max_K\|F_j\|\le1+\varepsilon_j\to1\). To construct them, approximate any continuous-holomorphic lift by polynomials, then correct its finite-dimensional evaluation error with a fixed polynomial right inverse. Choose analytic convex outer domains \(\Omega_j\to K\) sufficiently close that \(\max_{\Omega_j}\|F_j\|\le1+2\varepsilon_j\). The same singular pair works throughout.

**3. Pay the outer-domain limit.** The direct source gives, with \(\gamma_j\to2\),

\[
 0\le E_{B,j}
 =\int_{\mathbb T}\operatorname{tr}(\Delta_jJ\Delta_jJ)
 \le2(4/\gamma_j^2-1)a_j^2,
\]

where \(J=\operatorname{diag}(I_r,-I_s)\), \(Z=[X\ Y]\),

\[
 R_j=\zeta h_j'(\zeta)(h_j(\zeta)I-A)^{-1},\qquad
 \Delta_j=Z^*(R_j+R_j^*)Z\succeq0,
\]

and \(a_j^2=\int\|Y^*R_jX\|_{\rm HS}^2\).

This alone would be insufficient if \(a_j\) diverged. Convexity pays that issue: for the normalized exterior map \(h(\zeta)=c\zeta+\cdots\), the nonnegative boundary turning rate gives a probability measure \(\mu\) with

\[
 \log(h'(\zeta)/c)=2\int\log(1-u/\zeta)\,d\mu(u),
 \qquad |h'(\zeta)|\le4c\quad(|\zeta|\ge1).
\]

The enclosing domains have bounded \(c\), and their boundary resolvents are uniformly bounded because \(\sigma(A)\subset\operatorname{int}K\). Therefore \(a_j^2\) is uniformly bounded and \(E_{B,j}\to0\) absolutely. No Faber series or boundary derivative is passed to a nonsmooth limiting boundary.

**4. Exclude every simple supporting eigenvalue.** A positive matrix \(D\) with \(\operatorname{tr}(DJDJ)=0\) has a totally isotropic range for the form of signature \((r,s)\). Hence \(\operatorname{rank}D\le\min(r,s)\).

At a support point with a simple top eigenvalue of \(\operatorname{Re}(e^{-i\theta}A)\), the positive resolvent has rank three. Its compression by the full-rank \(Z\) has rank at least \(r+s-1>\min(r,s)\). Thus the slack density is strictly positive. Simplicity persists on an interval. Its support point cannot remain constant on that interval without producing a boundary eigenvalue. Choose two distinct endpoint support points; their approximating boundary arc has length bounded below. Cauchy–Schwarz gives a positive lower bound for the integrated slack, contradicting \(E_{B,j}\to0\).

This argument uses only support-point convergence and arclength, and covers corners and flat portions elsewhere on \(\partial K\).

**5. Finish with an elementary four-dimensional calculation.** Every top supporting eigenvalue is therefore repeated; applying the assertion in the opposite direction also repeats every bottom eigenvalue. After subtracting the trace, write \(A=B+iC\), with \(B,C\) traceless Hermitian. Every \(B+tC\) has eigenvalues \(s,s,-s,-s\), so

\[
 B^2=b^2I,\quad C^2=c^2I,\quad BC+CB=2dI.
\]

Diagonalize a nonzero \(B\) as \(b\operatorname{diag}(I_2,-I_2)\). Then the diagonal blocks of \(C\) are \(\pm(d/b)I_2\), and its off-diagonal block is a scalar multiple of a unitary. A block-unitary conjugation and a permutation give \(A\simeq_u B_2\oplus B_2\). The zero off-diagonal case would make \(K\) a segment and is excluded. Complete equality now occurs in the two-dimensional block, where scalarization on the same domain follows from step 1. Therefore \(\psi(A)=2\). This completes Theorem 4.

## Why the quadratic witness is preserved

For a column of scalar quadratics \(p_j\), square-function equality on a norming vector \(\xi\) gives \(p_i(A)p_j(A)\xi=0\). If \(m_\xi\) is its cyclic annihilator, then \(m_\xi\mid p_j^2\). Either \(\deg m_\xi>4\), forcing all \(p_j=0\), or the degree-at-most-two square-zero residue space has dimension at most one. Thus the output vectors are collinear and a unit scalar combination of the original entries attains two. Rows follow by adjoints.

Coefficient compression of an actual quadratic extremal preserves degree. In base dimension at most three it becomes a row or column. In base dimension four the remaining \(2\times2\) case is handled by the same positive-block argument, after which the derived two-dimensional summand allows scalar coefficient compression. This proves Theorem 4Q without an inverse-polynomial hypothesis.

## Active counterexamples and limits

- The supplied weighted-chain example remains valid: \(A=\left(\begin{smallmatrix}0&2\\0&0\end{smallmatrix}\right)\), \(P(z)=\left(\begin{smallmatrix}0&z\\1&0\end{smallmatrix}\right)\), and \(P[A]\) is the chain with weights \((1,2,1)\). It has no reducing norm-two nilpotent block. Its base norming pair has Schmidt ranks one and one, so scalarization extracts \(p(z)=z\). Adjoining a zero block gives a four-dimensional instance. It does not refute disk rigidity.
- One cannot replace arbitrary complete extremality by *attained quadratic* extremality. The four-dimensional Crabb matrix \(C_3\) has \(W(C_3)=\overline{\mathbb D}\) and \(\|C_3^3\|=2\). A quadratic matrix witness attaining two would, by Theorem 4Q and ACV's existing scalar classification, force a reducing \(C_1\) or \(C_2\) block, impossible for its single size-four Jordan block. The unrestricted theorem handles it through quotient lifts of unrestricted degree.
- No numerical-range stability exponent, effective modulus, dimension-five extension, or general claim about \(P[A]\)'s reducing subspaces is obtained. The metric companion is respected but not needed in the final argument. No converse from disk geometry alone is asserted.

## Prior art, substantiality and provenance

The primary comparison is recorded in [literature.md](../sources/i243_crouzeix_extremal_scalarization/literature.md). ACV already supplies rectangular extremals, scalar-tuple square functions, scalar polynomial classification and complete equality through dimension three. Hartz–McCarthy already supplies the first variation. Jin supplies scalar disk rigidity. BCD already supplies complete two-dimensional ellipse estimates. Those are not new findings here.

The additional deduction is the **uniform positive-block limit and rank obstruction**, followed by the dimension-four pencil argument. It proves an unrestricted complete equality implication beyond the inspected primary dimension-three theorem; the known two-dimensional block appears as a forced conclusion. This clears the specific direct-sum/ellipse and scalar-output overlaps in the brief. The bounded literature screen found no matching four-dimensional complete statement, but no literature-wide priority certificate is claimed.

Only assigned I243 files and fully read primary excerpts were written. No agents, live sibling contents, shared edits, staging, commits, publication, research code, tests, numerical experiments/scans, snapshots or seals were used. [reading-and-failures.md](../experiments/i243_crouzeix_extremal_scalarization/reading-and-failures.md) records the scope and corrected routes. [input-authentication.json](../experiments/i243_crouzeix_extremal_scalarization/input-authentication.json) records exact URLs, pinned source bytes/Git blobs/SHA-256 values, excerpt hashes and detached output hashes. The authentication file's own hash is returned separately.
