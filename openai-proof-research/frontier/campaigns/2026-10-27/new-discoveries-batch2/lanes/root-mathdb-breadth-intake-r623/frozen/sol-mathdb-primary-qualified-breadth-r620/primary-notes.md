# Selected primary-body screening; no novelty PASS

All four PDFs were fetched directly from versioned arXiv URLs with generic headers,
bound in source-provenance.json before pdftotext extraction. Derivatives were
bound before content searching. No MathDB requests or proof-registry requests.
No abstract is used as proof-body clearance. These are selected passages, not
whole-paper or full-dependency audits. No source is claimed current/latest.

## 378051: existing resolution

Original math/0309441v1 introduction, extracted lines 68–103, defines simple
G(n,c/n), uniform regular graphs, and I(n,c), I(n,r), and explicitly leaves
existence open beyond earlier ranges.

Bayati–Gamarnik–Tetali, *Combinatorial approach to the interpolation method and
scaling limits in sparse random graphs*, arXiv:0912.2444v2: inspected definitions
lines 160–198, independent-set model 228–233, Theorems 1 and 3 at 271–284 and
360–365, proof of Theorem 1 385–435, independent-set interpolation step 497–525,
regular independent-set step 1075–1108, and conclusion of Theorem 3 1244–1257.
These are actual body passages. Other model proofs, all of Theorem 7, and the
appendix near-superadditivity proof were not audited.

Theorem 1 treats fixed edge density. To pass to binomial G(n,c/n), couple a
uniformly ordered simple edge list with M~Binomial(n(n-1)/2,c/n). Its mean is
c(n-1)/2 and E|M-floor(cn/2)|=O(sqrt(n)); changing one edge changes independence
number by at most one. Hence the normalized expected difference tends to zero.
The source explicitly discusses transfer from non-simple to simple ensembles.
For regular graphs use Theorem 3 on rn even, condition on simplicity (probability
bounded below for fixed r) to retain convergence in probability. Since 0<=I/n<=1,
convergence in probability to the deterministic limit implies convergence in
expectation: E|X-a|<=epsilon+P(|X-a|>epsilon). This is the exact model/expectation
bridge, not a new discovery. Existing proof defeats eligibility; registry
unavailability cannot revive it.

## 381789: source already refutes universal r claim

arXiv:2212.04640v1, Conjecture 1.2/Theorem 1.3 and following discussion at lines
116–153; selected Lemma 3.8 construction/proof and Theorem 3.9 at lines 622–695.
At r=4 Theorem 3.9 gives sat(n,R(K4))=3n-6 for all sufficiently large n.
If the questioned formula held, 4n+C4=3n-6 for every sufficiently large n,
forcing C4=-n-6 for two distinct n: impossible. This public theorem already
defeats the universal claim; no new witness is proposed. The source explicitly
says r=3 is eventually true; do not copy the mirror prose asserting a
contradiction for every r>=3. The full Lemmas 3.3–3.7/lower-bound dependency
chain was not audited; the selected construction proof is not described as
full dependency verification.

## 379940: keep HOLD, no surrogate problem

Ionascu–Pritikin–Wright math/0608140v1: definitions section 2, Conjecture 1 and
Theorem 1 with beginning of its construction proof, extracted lines 70–225;
selected Theorem 4 statement/preceding comparison lines 680–710.
Half-dependent means 2|N(v) intersect S|<=degree(v) for v in S.
The boundary condition differs from mere 4-dependence. Conjecture 1 jointly
requires limit 3/5 and density >=3/5-C/n² for a single C and every n.
Theorem 1 provides residue-dependent losses typically linear in n in the
unnormalized count, so it does not establish the requested constant deficit.
Theorem 4 upper bound 0.608956 also does not establish 0.6.

checks.py exhaustively examines all subsets for n=1,2,3,4 and yields maxima
1,2,6,9. Five times deficits are -2,2,-3,3. This neither refutes any fixed-C
claim nor supplies a uniform boundary construction. No larger sweep or formal
investment warranted without a full-scope upper bound/certificate. No successor
body search was pursued because no viable full-scope route emerged; no prior
clearance claimed. The PDF arXiv banner is v1/2006 while its typeset draft line
says August 6, 2018; retain this internal date discrepancy, do not infer a new
version from it.

## 384464: literal wording test, no primary clearance

A=B=C, theta(z)=z, alpha(z)=conjugate(z) obey all displayed hypotheses:
|alpha z|=|z| and theta(z)+(theta(alpha(z)))*=2z, alpha(1)=1.
But norm(theta)=1. This only diagnoses the literal equality versus likely
upper-bound wording, which is categorically uncredited. The primary AIM route
remains parked, and the intended bound is not resolved here.
