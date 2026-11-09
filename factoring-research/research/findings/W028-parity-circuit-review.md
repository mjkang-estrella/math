# W028 review: finite Newton circuit and one parity split

2026-10-08 local. **Accept the rational representation, the degree count over Q, and the four-state straight-line program. They do not extract the central binomial coefficient below dense degree. No consumer of this circuit is faster than the ordinary length-m product. Verified complete factoring improvement: NONE.**

Frozen parent texts: [W028-rational-newton-coefficient.md](W028-rational-newton-coefficient.md) SHA-256 `cdd5f1d84a543baca09b4251ce886615b5f6989543e68f964ca3d1d9ef0dc370`, and [W028-parity-state.md](W028-parity-state.md) SHA-256 `b02a036e8be6dffa10c8712e29c7633b93f89c3b3c04680c723cc8aa58705abd`. The assignment, hashes, and read scope are in [W028-parity-circuit-review-evidence](W028-parity-circuit-review-evidence/). W022 is used only at the given interface: some specific central-binomial residue splits a scoped semiprime family, and acquisition is not fast. W023, W026, and W027 were not re-audited. No numerical run was made.

Throughout, \(N\) is odd, \(A=1-4t\), \(n=2^k\), and \(d=n/2\). The ring \(\mathbb{Z}/N\mathbb{Z}\) is not a field.

## 1. The Newton identities are exact

Start with \(P_0=Q_0=1\) and
\[
P_{k+1}=P_k^2+A Q_k^2,\qquad Q_{k+1}=2 P_k Q_k.
\]
The residual identity \(P_k^2-A Q_k^2=(4t)^n\) and the evaluation \(P_k(0)=Q_k(0)=2^{n-1}\) follow by induction from \(1-A=4t\) and \(A(0)=1\). Both polynomials lie in \(\mathbb{Z}[t]\). For odd \(N\), the constant \(2^{n-1}\) is a unit, so \(Q_k/P_k\) is a well-defined series in \((\mathbb{Z}/N\mathbb{Z})[[t]]\).

Let \(a^2=A\). Binary expansion of \(1+a\) gives the closed form
\[
P_k+a Q_k=(1+a)^n,\qquad P_k-a Q_k=(1-a)^n,
\]
because the square of \(P+aQ\) is the same Newton step and the initial value is \(1+a\). Equivalently, the straight-line program is repeated squaring in the degree-2 algebra \(\mathbb{Z}[t][a]/(a^2-A)\). It has \(O(k)=O(\log n)\) additions and multiplications in that algebra. There is no truncation gate in this description. An arithmetic gate here is one operation on the current algebra element, not one operation on a coefficient.

The two series square roots of \(1/A\) differ by a series whose sum with \(Q_k/P_k\) has constant term 2. For odd \(N\), that sum is a unit in the power-series ring, and the residual is divisible by \(t^n\), so
\[
\frac{Q_k}{P_k}\equiv (1-4t)^{-1/2}\pmod{t^n}.
\]
The binomial series of the right-hand side is \(\sum_{m\ge 0}\binom{2m}{m}t^m\). Therefore the coefficients agree for every index \(m\) with \(0\le m<n\), and for no larger range in general. The proof inverts only powers of 2. It does not invert a factorial or an integer whose gcd with \(N\) is unknown.

The boundary is sharp. For \(k=2\), \(n=4\),
\[
P_2=16t^2-32t+8,\qquad Q_2=8-16t,
\]
and \(Q_2/P_2=(1-2t)/(1-4t+2t^2)\). Its coefficients through degree 4 are \(1,2,6,20,68\). The central binomials are \(1,2,6,20,70\). Agreement holds exactly through degree \(n-1=3\).

For \(k\ge 1\), \(\deg P_k=n/2\) and \(\deg Q_k=n/2-1\). The leading term of \(P_{k+1}\) comes only from \(P_k^2\), because \(\deg(A Q_k^2)=n-1\) while \(\deg(P_k^2)=n\). The leading coefficient is \(-4\) at \(k=1\) and \(2^n\) for every \(k\ge 2\). The leading coefficient of \(Q_k\) is likewise \(\pm\) a power of 2, by \(Q_{k+1}=2 P_k Q_k\). Both are units modulo odd \(N\). So these two degrees are exact in \((\mathbb{Z}/N\mathbb{Z})[t]\), not merely upper bounds. Exactness of \(\deg P_k\) does not determine the reduced degree of a later section modulo a prime, and it does not make a coefficient free.

Logarithmic differentiation of the closed form, using \(da/dt=-2/a\) and \((1-a)(1+a)=4t\), gives the rational identity
\[
\frac{Q_k}{P_k}=1-\frac{2t}{n}\frac{P_k'}{P_k}.
\]
If \(\lambda_1,\ldots,\lambda_d\) are the reciprocal roots of \(P_k\), the logarithmic derivative plus \(d=n/2\) cancels the constant and leaves
\[
\frac{Q_k}{P_k}=\frac{2}{n}\sum_{i=1}^d\frac{1}{1-\lambda_i t}
\]
as rational functions, not merely through degree \(n-1\). The Taylor coefficient of degree \(m\ge 0\) is therefore \((2/n)\sum_i\lambda_i^m\). It equals \(\binom{2m}{m}\) for \(0\le m<n\), and the \(n=4\) coefficient 68 shows that the equality stops there.

The substitution \(\lambda=\eta+2+\eta^{-1}\) with \(\eta^n=-1\) is the root condition \((1+a)^n=-(1-a)^n\). For \(k\ge 1\), \(n\) is even, so \(\eta\ne\eta^{-1}\) on this set. Inverse pairs give one \(\lambda\), and
\[
\lambda=4\cos^2(\theta/2),\qquad \theta=\pi(2j+1)/n,
\]
runs through \(d\) distinct values in the real interval \((0,4)\). The sum of \(\lambda_i^m\) is half the sum of \((\eta+2+\eta^{-1})^m\) over the \(n\) roots of \(z^n+1\). For \(0<m<n\) that Laurent polynomial has exponents in \([-m,m]\), and
\[
\sum_{\eta^n=-1}\eta^r=n(-1)^{r/n}
\]
when \(n\) divides \(r\), and equals 0 otherwise. The only such exponent in range is \(r=0\), where the sign is \(+1\), so the full sum is \(n\binom{2m}{m}\). Multiplying by \(2/n\) and taking half returns \(\binom{2m}{m}\). The trace in \(\mathbb{Q}[z]/(z^n+1)\) has restated the coefficient. The same power sum is the trace in the degree-\(d\) pole ring, which is still \(\Theta(m)\) data when \(m<n\) and \(n\) is the least power of two above \(m\). Neither trace is a gate.

## 2. Sections keep degree \(d\) over \(\mathbb{Q}\)

For \(a\ge 1\) and \(0\le c<a\), the series section that keeps indices congruent to \(c\) modulo \(a\) is
\[
\frac{2}{n}\sum_{i=1}^d\frac{\lambda_i^c}{1-\lambda_i^a t}.
\]
On the positive reals, \(x\mapsto x^a\) is injective, so the \(d\) poles \(\lambda_i^a\) stay distinct. Each weight \(\lambda_i^c\) is positive. A simple pole with nonzero residue survives in lowest terms, so the reduced denominator has degree exactly \(d\) over \(\mathbb{C}\) and hence over \(\mathbb{Q}\). The denominator polynomial itself lies in \(\mathbb{Q}[t]\) because it is the resultant of \(C_d(X-2)\) with \(Y-X^a\), up to the monic normalization below. This is a statement about the exact rational function. It is not a circuit lower bound, and the positive-real separation is not a proof over a prime field or over \(\mathbb{Z}/N\mathbb{Z}\).

The one-step denominator can still have exact degree \(d\) as an unreduced polynomial modulo odd \(N\), because it is essentially \(P(t)P(-t)\) and the leading coefficient of \(P\) is a unit. Cancellation in lowest terms modulo a prime is a separate question. No such cancellation is claimed or ruled out here.

## 3. The four-state split is a straight-line program

Write \(z=t^2\), \(P=E(z)+t O(z)\), and \(Q=G(z)+t H(z)\). Expanding \(P^2+A Q^2\) and \(2PQ\), and separating even and odd parts, produces exactly
\begin{align*}
E_+&=E^2+z O^2+G^2+z H^2-8z GH,\\
O_+&=2EO+2GH-4G^2-4z H^2,\\
G_+&=2(EG+z OH),\\
H_+&=2(EH+OG).
\end{align*}
The initial state \((E,O,G,H)=(1,0,1,0)\) is \((P_0,Q_0)\). Each step uses \(O(1)\) additions and multiplications, so \(k\) steps are \(O(k)\) gates in the polynomial ring. Those gates do not emit coefficients.

Multiplying the numerator and denominator by the denominator at \(-t\) gives the transformed denominator \(E^2-z O^2\), the even numerator \(GE-z HO\), and the odd numerator \(HE-GO\). The new constant term is \(E(0)^2=2^{2n-2}\), still a unit for odd \(N\).

This state does not iterate at constant width. After the split, the denominator is \(E^2-z O^2\), whose roots are the squared reciprocal poles, and the parent pole count says there are still \(d\) of them over \(\mathbb{Q}\). A second parity decomposition has eight component polynomials. The document's two concrete accountings remain: \(a=2^j\) base-\(t^a\) components, or a coefficient prefix of length \(m\) stored as \(a\) blocks of precision about \(m/a\). Both store on the order of \(m\) explicit coefficients when \(d=\Theta(m)\). That is the cost of those representations. It is not a lower bound on every circuit.

The \(n=4\) even section is a witness that the degree does not halve. The four-state values are \(E=8+16z\), \(O=-32\), \(G=8\), \(H=-16\), and the even function in lowest terms is
\[
\frac{1-6z}{4z^2-12z+1}.
\]
The denominator is coprime to the numerator and has degree \(2=d\), not \(1\). Its roots are \(1/(2\pm\sqrt{2})^2\).

## 4. Chebyshev packaging

Let \(T_d\) be the Chebyshev polynomial of the first kind and set \(C_d(X)=2 T_d(X/2)\). For \(d\ge 1\) this is monic, because the leading coefficient of \(T_d\) is \(2^{d-1}\). The identity \(T_d(\cos\theta)=\cos(d\theta)\) puts the reciprocal poles at the roots of \(C_d(X-2)\). The duplication \(T_{2d}(x)=2 T_d(x)^2-1\) is \(C_{2d}(X)=C_d(X)^2-2\). Since \(d\) is a power of two, repeating this from \(C_1(X)=X\) is an \(O(\log d)\) straight-line program for the monic pole polynomial. Expanding that program writes \(d+1\) coefficients.

The symmetry \(\lambda\mapsto 4-\lambda\) is the sign symmetry of the Chebyshev roots about 0, translated by 2. Parity extraction sends \(\lambda\) to \(\lambda^2\). Those maps are different, and the degree count forbids replacing the section by a Chebyshev polynomial of degree \(d/2\). Naming the section denominator as the resultant of \(C_d(X-2)\) and \(Y-X^a\) does not compute the resultant.

## 5. What Bostan–Mori actually prices

The parent locator "PDF text lines 454–548, including the effective-ring setup" does not match this file. In the downloaded author PDF, footnote 0 on page 1 is the effective-ring hypothesis, and Algorithm 1 is in §2.1. The details and both `pdftotext` numberings are in [BoMo21-locations.md](W028-parity-circuit-review-evidence/sources/BoMo21-locations.md). The theorem underneath the locator is right.

Algorithm 1 takes the coefficient arrays of a numerator of degree less than \(d\) and a denominator of degree \(d\), with the denominator constant invertible in a commutative ring. Each step multiplies those polynomials, keeps one parity, and squares the constant in the sense \(V(0)=Q(0)^2\). The only division is the final division by that unit. No field hypothesis is used. The printed cost is \(2\mathrm{M}(d)\lceil\log(N+1)\rceil\) ring operations. Theorem 1 packages the same bound from \(d\) recurrence coefficients and \(d\) initial terms. Fiduccia's earlier algorithm, as cited there, has the same dependence on a dense order-\(d\) input.

Applied to \(Q_k/P_k\), this requires the expanded coefficients of a degree-\(d\) denominator. The \(O(\log n)\) straight-line program is not that input. Expanding it by dense repeated squaring already costs \(\sum_{j<k}\mathrm{M}(2^j)=\Theta(\mathrm{M}(d))\) coefficient operations. One coefficient of a fixed rational function of degree \(d\) then costs another \(O(\mathrm{M}(d)\log m)\). For the prefix \(m<n\), one has \(d=\Theta(m)\) after the usual choice \(n<2m\). The resulting cost is on the order of \(m\) coefficients times at least a logarithm under fast multiplication, and it is quadratic in \(m\) under schoolbook multiplication.

Footnote 8 of the same paper prices the Nth Chebyshev polynomial at \(O(\mathrm{M}(N))\) and calls that quasi-optimal. Constant-order binary powering, such as the scalar Fibonacci shortcut in their Algorithm 4, applies to a recurrence whose order does not grow with the index. It does not apply to a denominator of degree \(\Theta(m)\).

## 6. Prior art for this coefficient

The sequence is holonomic of order 1:
\[
\binom{2m}{m}=\prod_{j=1}^{m}\frac{4j-2}{j}.
\]
This is an identity in \(\mathbb{Z}\). Modulo odd \(N\) it is the direct scalar consumer.

- If \(\gcd(j,N)=1\), the step multiplies by \(4j-2\) and by the modular inverse of \(j\).
- If \(1<\gcd(j,N)<N\), that gcd is a nontrivial factor of \(N\). The inversion is not legal, and the attempt has already split \(N\).
- If every prime factor of \(N\) exceeds \(m\), every \(j\le m\) is a unit and the product uses \(\Theta(m)\) multiplications and inverses in \(\mathbb{Z}/N\mathbb{Z}\). It never consults \(P_k\), \(Q_k\), or the four-state program.

So the admissible composite operations are: the Newton and four-state ring operations, inversion of powers of 2, one Bostan–Mori step on arrays whose constant is a power of 2, and the product step above when \(j\) is a unit. The trace, an SLP coefficient gate, and a degree count over a prime field are not operations in this list.

Bostan–Christol–Dumas, arXiv:1602.00545v2, state two further algorithms for the Nth coefficient of an algebraic series, which covers \((1-4t)^{-1/2}\). In characteristic zero, the best bound they record is the Chudnovsky baby-step/giant-step method, quasi-linear in \(\sqrt{N}\) arithmetic operations. Over the prime field \(\mathbb{F}_p\), they state an \(O(\log N)\) bound after a precomputation quasi-linear in \(p\). Both statements are field statements. The second needs the prime. Neither is an algorithm over unknown odd \(\mathbb{Z}/N\mathbb{Z}\), and this review did not promote either one to that ring. In particular, the \(O(\log n)\) Newton program is not their prime-field automaton algorithm, and their characteristic-zero bound is not a polynomial-time factoring result.

No checked source gives a straight-line program of size \(O(\log m)\) for \(\binom{2m}{m}\) in \(\mathbb{Z}/N\mathbb{Z}\). The compressed objects that do exist are compressed representations of \(P_k\), \(Q_k\), or \(C_d(X-2)\). Reading one Taylor coefficient from those representations is the unpaid step.

## 7. Disposition

The parent claims that were audited are accepted with the boundaries in §§1–5. The line-range citation is wrong and does not change Algorithm 1's hypotheses. The \(O(\log n)\) figure counts straight-line gates for repeated squaring. It does not count coefficient operations, bit operations, or a factoring runtime.

The scalar-coefficient hope fails on this circuit. Every section examined over \(\mathbb{Q}\) keeps reduced degree \(d\). The one parity split that stays inside a four-word Newton state still represents a degree-\(d\) rational function. Bostan–Mori then charges for those \(d\) coefficients. The ordinary product charges \(\Theta(m)\) unit operations in the case where it is legal, and charges a factor when it is not. Either accounting is an acquisition of the binomial residue. Neither runs in \(O(\log n)\) ring operations. Neither uses a hidden coefficient gate in the Newton program.

There is no concrete next consumer of the four-state state. The computation that actually returns the residue is the length-\(m\) product, with the gcd branch above; it does not read the Newton state, and it is not cheaper than dense degree. A later modular drop in section degree, or a transfer of the Chudnovsky or prime-field bounds to odd composite moduli, would be a new algorithm with its own hypotheses. This audit does not supply that algorithm.

No solver, Lean, STATE, or task file was changed. No package was installed. No subagent was started. No experiment, sweep, or rerun was performed. **Verified complete factoring improvement remains NONE.**
