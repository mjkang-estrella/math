# Primary-body operation comparison: B8C contribution round 2

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0;
original code MIT. Third-party rights retained privately.

**Contribution: UNRESOLVED. Mathematics: retained PASS_FULL_B8C. Counted=false.**

The exact proposed contribution is a configuration C of nine unit rays in C^3
such that

    alpha(C) := min_[u] max_s in C |s*u|^2 > 1/2.

Writing rho(C)=max_[u] min_s sqrt(1-|s*u|^2), this is rho(C)<1/sqrt(2).
With d_FS([u],[s])=arccos|s*u|, it is R_FS(C)<pi/4. All extrema range
over the ENTIRE CP^2. A bound on pairwise center separation or a mean over
targets does not assert this. A certified earlier construction satisfying
these precise hypotheses would already give B8C's upper half: put each
projector into its closed maximum-overlap cell; Bessel excludes orthogonal
pairs and compactness gives attained diameters <sqrt(2). The antecedent
Hermitian lower bound would then give b(X)=9. No such earlier certificate
was identified in this round; this is a bounded reading result, not an
assertion that none exists.

## Mondal–Heath: the previously inaccessible body now compared

Bishwarup Mondal and Robert W. Heath Jr., *A Diversity Guarantee and SNR
Performance for Unitary Limited Feedback MIMO Systems*, DOI
[10.1155/2008/594928](https://asp-eurasipjournals.springeropen.com/counter/pdf/10.1155/2008/594928.pdf),
Theorem 1, (7)/(10), Appendix A (A.1)–(A.6), and Appendix C were read.
The metric controlling diversity is ||FF*-GG*||_2. Their condition is a
uniform covering radius delta<1, equivalent to covering by linear
complements. The proof first turns distance<1 into transversality, then
uses continuity and compactness for a strict global bound. Section 3.3
invokes Clark–Shekhtman for the cardinality Ms(Mt-Ms)+1; Lemma 1/Appendix C
supplies antenna-selection codebooks. Section 4's (20)–(28) instead
controls expected SNR and asymptotic expected chordal distortion. It
neither supplies a quantitative strengthening of delta<1 to delta<1/sqrt(2)
nor exhibits nine centers with that strengthening. These are actual proof
operations, not conclusions guessed from the word “covering.”

Here is the independent specialization and a strict logical separation.
On the span of two unit vectors, P_u-P_s has nonzero eigenvalues
+/-sqrt(1-|s*u|^2). Consequently their projection metric in G_{3,1}
is exactly the rho metric above, and their theorem says alpha(C)>0.
For their coordinate antenna-selection example,

    max_j |u_j|^2 >= 1/3,

with equality at the flat vector, so alpha=1/3 and delta=sqrt(2/3).
Even N=9 and full spanning do not bridge the thresholds. Take the three
coordinate rays and the six rays e0+(k/100)e1, 1<=k<=6, normalized.
They are nine distinct spanning rays. At u=(1,1,1)/sqrt(3) every score
is at most (1.06)^2/3 < 1/2, whereas the coordinate rays ensure alpha>=1/3.
Thus this is a covering codebook in their sense and fails the target.
The counterexample refutes an implication from their hypotheses, not
existence of other good nine-center codebooks.

Normalization caution: the retained PDF's (9) prints the Frobenius norm
of the projector difference without 1/sqrt(2), while nearby prose says
it coincides with d_P for lines. Those printed expressions differ by
sqrt(2). Page 5 was visually inspected; the comparison uses their
unambiguous spectral-norm equation (7), not a silent normalization repair.
No conclusion here depends on the normalization of their SNR formula.

## Following the complements and quantization citations

Clark–Shekhtman, *Covering by complements of subspaces, II*, Proc. AMS
125 (1997), 251–254, DOI
[10.1090/S0002-9939-97-03535-1](https://www.ams.org/proc/1997-125-01/S0002-9939-97-03535-1/),
was read in its author-uploaded full body. Lemmas 1–3 use exterior products
and projective dimension for the lower bound. Lemma 4 removes a bad
incidence variety of smaller dimension to obtain k(n-k)+1 subspaces;
Remark 1 explains genericity. There is no prescribed angular separation
from that bad variety. For k=1,n=3, spanning lines suffice to complement
every hyperplane; three coordinate lines already do. This operation
establishes qualitative nonvanishing, not the Bessel threshold. Its
algebraically closed field hypothesis also does not encode a Hermitian
angular constant.

Mondal–Dutta–Heath, *Quantization on the Complex Projective Space*, DCC
2006, DOI [10.1109/DCC.2006.68](https://www.researchgate.net/publication/4229998_Quantization_on_the_complex_projective_space),
was read in the author-uploaded DRAFT body. Equation (4) is sin of the
principal angle; (5) integrates distortion against a source density.
Lemma 1 computes average radial distortion in a ball. Lemma 2 compares
a cell's integral with that of an equal-volume ball. Equations (19)–(27)
then use high resolution and point densities for an asymptotic LOWER
bound on expected distortion; the conclusion explicitly limits the
heuristic derivation. An equal-volume comparison is not a containment
statement about all points of that cell. It supplies neither a nine-point
worst-case upper bound nor an explicit non-SIC perturbation certificate.
The authenticated r1 Dai–Liu–Rider comparison concerns the same expectation
versus supremum distinction; its full reading is not inherited as this
round's reading.

## Packing-to-codebook calculations do not provide the missing quantifier

Love–Heath–Strohmer, *Grassmannian Beamforming for Multiple-Input Multiple-
Output Wireless Systems*, [journal body](https://people.ece.ubc.ca/paull/teaching/eece_496/GB_MIMO_WS_Love_Heath_Strohmer.pdf),
Sections III–IV, derives the disjoint-ball density N(delta/2)^(2(m-1)),
Hamming/Gilbert–Varshamov packing bounds, and an expected-loss bound.
The proof of (20)–(21) explicitly splits targets inside the disjoint
packing balls from the remainder, where it uses the trivial loss bound 1.
Its proposed criterion maximizes minimum center distance. It does not
prove every target belongs to those balls. The June 3, 2003 author
preprint has the corresponding equations (24)–(26); the two versions'
numbering was kept separate. For the Hesse packing, minimum distance
sqrt(3)/2 by itself therefore cannot be promoted to rho<1/sqrt(2).

Pitaval–Määttänen–Schober–Tirkkonen–Wichman,
[2011 author PDF](https://users.aalto.fi/~oltirkko/pubs/Pitaval2011_TIT.pdf),
III.B (7)–(10), explicitly presents packing as a surrogate for expected
distortion. V.A, Lemma 1/Proposition 1, proves the half-angle map and
isometry from C^2 lines to a real sphere of radius 1/2. These operations
are valuable actual codebook constructions, but concern CP^1. A spherical
nine-point configuration transported by that map remains in CP^1; embedding
it into C^3 leaves the orthogonal third coordinate ray with score zero.
This does not produce the requested CP^2 cover.

## A newer direct covering construction and an exact exclusion

Riasat–Mahdavifar, *Covering in Hamming and Grassmann Spaces: New Bounds
and Reed–Solomon-Based Constructions*,
[arXiv:2512.22911v1](https://arxiv.org/html/2512.22911v1), III.A (6)–(9)
distinguishes maximum from average covering. Theorem 2's beta-distribution
proof evaluates the expected average radius of a random code. V, (46),
constructs CRS vectors from additive characters. Theorem 8's statement
bounds average radius under independent amplitude/phase assumptions;
the read proof portions use Markov and expectation bounds. These statements
are not finite-code uniform certificates. The complete Theorem 8 proof was
not read and is not needed for the following exclusion.

Independently of its code size, every normalized length-three vector in
(46) has coordinate magnitudes 1/sqrt(3). Thus each coordinate ray e_j
has score exactly 1/3 against EVERY codeword: alpha(C)<=1/3. A common
unitary rotation merely rotates those witness rays. Hence this entire
constant-modulus class cannot meet alpha>1/2 in CP^2. This is a precise
comparison of the actual construction, not an inference that all modern
covering codebooks fail or that no other construction exists.

## Antecedent Hesse geometry and the proposed additional operation

The pinned real-projector method already pays open enlargement, homogeneous
integration, spectral subtraction, and the odd-map bound. Its Hermitian
transfer receives no substantiality credit. The r1 body comparisons of
[Hughston–Salamon](https://arxiv.org/html/1410.5862v2) and
[Dang–Blanchfield–Bengtsson–Appleby](https://arxiv.org/html/1211.0215v2) establish the
antecedent SIC/WH/Hesse framework. This round reread the latter's (22)–(24)
and the former's classification statement and selected WH/SIC interfaces,
without claiming another full classification reading. Their locus requires
squared mutual overlaps 1/4, while the candidate leaves that locus:

    p q = 1/4 - epsilon^2/(2(1+epsilon^2)^2),
    |<f_epsilon,Z f_epsilon>|^2 = 1-3 p q > 1/4,
    cross-coordinate-zero-group scores between centers = p q < 1/4.

Here p,q are the two nonzero coordinate probabilities. These formulas
follow directly from the frozen fiducial. Thus its non-SIC orbit is
permitted even though SIC classification is complete. Its extra operation
is the cyclic successor assignment in each of four MUB bases; WH covariance
preserves that assignment; one tangent has positive real derivative products
at its four assigned poles. The essential uniform step is then the two-trio
estimate on all complex z2,z3, including scales where the favored spatial
linear term vanishes. Improving the twelve old holes alone is insufficient:
the minimizer could move. Lemma 11, followed by compactness away from the
holes, supplies the uniform operation that the compared codebook bodies
do not supply. This description preserves the r1 proof PASS, not a new
proof review or a worldwide priority claim.

## Decision and exact remaining question

UNRESOLVED is retained. SUBSTANTIAL would require a defensible comparison
against the closest finite worst-case covering antecedents, not just the
elimination of these mismatched implications. TECHNICAL is not justified
merely because the proof is short or the lower half is transferred.
DUPLICATE requires an identified antecedent with a sufficient theorem or
construction, which this review has not obtained. No numeric nine-center
covering table was located and certified; no sampled optimum is used.

The remaining primary question is: does an earlier nine-ray codebook in
C^3, proved non-SIC WH cover, or fully instantiated finite-size theorem
establish rho<1/sqrt(2), and does its proof already perform the cyclic
assignment and uniform resolution of all Hesse/MUB neighborhoods? An earlier
existence theorem could make the statement antecedent even with a different
proof; an earlier same-operation proof could establish duplication more
strongly. The literature gate remains open on that precise question.
The named Mondal–Heath access obstruction is resolved; its body is not a
solution of the remaining comparison. Missing hits, unrelated finite-field
codes, and uninspected citations do not establish novelty.
