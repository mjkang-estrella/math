# Source, full scope and mathematical attempt

The primary source is https://arxiv.org/html/2610.38469v1 and its actual source https://arxiv.org/src/2610.38469v1. The saved unversioned abstract records submission 28 October 2026 08:45:17 UTC, v1 only. The arXiv DOI is 10.48550/arXiv.2610.38469. The bibliography's data DOI10.5281/zenodo.23698148 supplies the companion archive; the denied GitHub route was not used. Actual URLs, access UTCs, byte sizes and hashes are in http.jsonl.

Let K have characteristic zero, n>=3, Phi_n=K[x_0,...,x_(n-1)]/(x_i^2), with cyclic indices. Set Y_i=x_(i+1)-x_i-x_i*x_(i+1), and F_d=span of all products of at most d Y_i, including 1. H_n(t)=sum_d(dim F_d-dim F_(d-1))t^d. This is the literal nonzero-quadratic-coefficient case by source Proposition3.14, not the linear/degenerate cases. The source transfer matrix has characteristic polynomial z^3-z^2-3tz+2t. Write T_n=tr(M^n). Conjecture7.8 asks H_n=T_n-t^2 modulo t^ceil(n/2), universally in n. Its independent-set statement weights an independent set S by 3^c(S), where c counts unselected vertices with both neighbors selected. The cumulative identity to prove is

    rank_Q A_(n,d) = sum_(j=0)^d [t^j]T_n - 1_(d>=2), for every 2d<n,
    (A_(n,d))_(S,m) = product_(i in S)(m_(i-1)-m_i),
    S subset Z/n, m nonnegative integer vector, |m|<=d.

Source Theorem7.1 proves degrees through3 in their stable ranges. Theorem7.3 fixes the top coefficient; Proposition7.9 shows how a full stable-range proof determines all H_n. Neither is reclaimed here. The boundary-operator rank formulation following Remark7.11 likewise remains open in the actual source. The first new degree for an all-degree argument is4, but solving degree4 alone would not resolve the assigned target.

## Attempt1: multivariate Newton coordinates

For any polynomial q(m), define C_(S,a)=Delta_1^a1 ... Delta_n^an q_S(0), where q_S(m)=product_(i in S)(m_(i-1)-m_i) and |a|<=d. Explicitly

    C_(S,a)=sum_(0<=b<=a) (-1)^(|a|-|b|) product_i binom(a_i,b_i) A_(S,b).

This is an integer unitriangular column transformation on the finite lower simplex, hence rank C=rank A over Q (indeed over every field). Its inverse is q(m)=sum_(a<=m) C_a product_i binom(m_i,a_i), for every simplex node m. This follows directly by binomial inversion in each coordinate; all b<=a stay in the lower simplex. There is no limiting argument.

The tempting benefit is locality: each m_i occurs in at most two factors of q_S, so columns with a_i>=3 vanish. However E(m)=product_i(1+(m_(i-1)-m_i)x_i)=exp(sum_i m_i(x_(i+1)-x_i)) in Phi_n. Applying a forward difference in m_i multiplies E(m) by exp(x_(i+1)-x_i)-1=Y_i. Therefore C_(S,a) is exactly the coefficient of x_S in product_i Y_i^a_i. This is the original product matrix, not a smaller independent rank computation. Counting its nonzero columns or their supports is not a proof of independence. The route is an exact reformulation but fails to produce the uniform basis needed for the target.

## Attempt2: straightening from the source's low-degree relations

Put R=2 sum z_i - sum z_i^2. Exact evaluation gives R(Y)=0, Y_i^3=0, and Y_i^2Y_(i+1)+Y_iY_(i+1)^2=0. The source proves these account for all degree<=3 relations in the stable range. A naive extension using only their multiples whose displayed degree stays<=d was tested. At n9,d4, the word space has715 columns. Over F_1000003 the evaluation rank is435 and this known-relation span has rank226. Consequently its codimension inside the finite-field kernel is715-435-226=54. The output intentionally says 'over_test_field': a modular rank is a lower bound on rational rank and does not authenticate this codimension over Q.

There are further exact local quartics. For three consecutive generators a,b,c (five or more vertices to avoid accidental wrap),

    2a^2bc+a^2c^2=0,   2abc^2+a^2c^2=0.

Indeed a^2=-2x_i*x_(i+1), c^2=-2x_(i+2)*x_(i+3), and direct multiplication gives a^2bc=abc^2=-2x_i*x_(i+1)*x_(i+2)*x_(i+3), while a^2c^2=4 times that monomial. These hold exactly, but no claim is made that adjoining them generates the whole kernel. They are not nominations or a solution of an independent question. A full straightening route still requires all-degree rules, a terminating order and a proof of all overlaps, with normal-form count T_n-t^2 below half length. There is no induction step here that supplies those facts.

## Attempt3: closing the path transfer / matching quotient

The source's path-state calculus counts separately realizable boundary states. It does not prove that the cyclic path coefficients all come from one polynomial. The remaining source map D_(n,d) takes all coefficient extractions modulo the appropriate open-path annihilator, and the target is its rank. Local dimensions alone do not determine a cyclic kernel: even invertible two-dimensional transports Q_i all have the same local rank, whereas equations v_(i+1)=Q_i v_i have solution space ker(I-product Q_i), which has dimension2 for all Q_i=I and dimension1 if exactly one Q_i=diag(1,-1). This illustrates the missing monodromy constraint; it is not a counterexample to the source conjecture.

The material actual body Grinberg–Kirillov–Shapiro, arXiv2609.34260v2, Theorem5.16 and proof, gives the Dunkl matching algebra Hilbert series for a unicyclic graph: matching polynomial minus t times the matching polynomial after removing cycle vertices. On C_n this is I(C_n;t)-t. But this algebra kills incident edge products; our Y_i lives in the larger algebra where adjacent edge products survive. The source identifies this as its quotient by J=(x_i*x_(i+1)). That quotient gives no induced filtration on J. Replacing its Hilbert series by the claimed full series omits exactly the unresolved data. No complete classical subsumption bridge was found; merely invoking transfer matrices, binomial inversion or matching theory does not settle eligibility either way.

## Exact universal gap and disposition

It remains to prove (or refute) the displayed rational rank identity simultaneously for every n>=3 and every d<n/2. An all-degree basis or full cyclic-compatible annihilator description would suffice; only a transform back to the product matrix and local relations were obtained. The known source top term, quotient dimensions, finite checks and local path ranks do not close it. No complete ordinary theorem has arisen, so no PROOF.md certifying a source resolution is issued. Ordinary mathematics: UNRESOLVED. Novelty/eligibility: HOLD, no nomination. Counts unchanged.

## Historical and public-proof screening limits

history-receipt.json reuses the r169 index, itself qualified from r168/r167 and earlier indexes, refreshes hashes/new immediate original reports and records13 changed/new entries out of1729. sources/history-qualification.json retains exact original/counterpart provenance, including original r111–113 science; no date or whole-lane exclusion is used. Title/author/arXiv audit was completed before primary body retrieval; DOI and statement-alias expansion followed before mathematical investment. The unrelated r117 numbered Conjecture7.8 hit is not this source. Eccentricity metadata was an abandoned discovery lead, with no claimed result.

registry-original-screen.json screens the actual three saved tree files referenced by r169's fixed-current receipt, with exact hashes and bounded hits. Other saved screens and path lists are separately identified in saved-registry-screen.json. These are bounded source selection aids, not path-absence or novelty certificates; no matching body was selected by these aliases. We did not read every unselected proof body, refresh current HEADs or retry denied GitHub APIs/raw/codeload/patch/diff/ScienceDirect requests. Thus no completed current global prior screen is asserted.

Exact inherited limits remain in sources/historical-steiner-limits.md and sources/historical-pendulum-limits.md: aa026->a19a and a19a->490f capped histories; missing merge-result/parent trees for f445b165 and related transitions; OpenAI fixed4eaee875 has281 listed paths with105 actual patches and176 absent patches, and its full recursive-tree request403. Omega fixed2b143c68 and old complete subtree listings are only their recorded snapshots. The Steiner citation10/19 HOLDs remain their original target's obligations, not newly asserted zonotopal companions. No failed offline reconstruction was repeated. Matching unread bodies and missing historical bytes are not declared cleared. No badge, empty solution array or worldwide priority assertion is used.
