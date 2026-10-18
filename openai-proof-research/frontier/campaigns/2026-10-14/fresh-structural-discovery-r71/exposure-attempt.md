# Concrete attempt: typical-row entropy through adaptive deletion

## Unchanged motivating question

For every fixed p in (0,1) and every fixed integer k>=2, let A_n be symmetric with independent upper-triangular entries, each +1 with probability p and -1 with probability q=1-p. The desired full conclusion is

lim_{n->infinity} P(corank(A_n)>=k)^(1/n) = p^(k+1)+q^(k+1).

This is an exploratory target, not a theorem or frozen candidate. Requiring k+1 equal rows supplies the lower event with exact probability

[p^((k+1)(k+2)/2)+q^((k+1)(k+2)/2)] [p^(k+1)+q^(k+1)]^(n-k-1).

The upper bound is unpaid. The r68 circuit-contraction lemma bounds the mass of a fixed homogeneous rank-k section by f(k+1), where f(t)=p^t+q^t. Its extremizer/gap proof does not license adaptation to revealed symmetric entries, affine translated fibers, or approximate kernels.

## Attempt and actual source interface

The inherited source path argument charges a rare column by max(p,q)^(n-o(n)) and a width-two gate by max(p,q)^(2n-o(n)). For corank two the latter may exceed f(3)^n: at p=1/10, q^2=.81 while f(3)=.73. Merely relabeling its exception as a higher-corank bound fails.

A concrete possible repair was to select every costly deletion among original rows having approximately pn positive entries. A specified such column, after o(n) deletions, has original probability exp(-H(p)n+o(n)), where H(p)=-p log p-q log q. Tracking original signs is essential: conditioning the anchor flips signs and produces independent but nonidentically biased bits. Two charged typical columns would give exp(-2H(p)n+o(n)), strictly below f(3)^n. More generally k typical columns would give exp(-kH(p)n), below f(k+1)^n by monotonicity of Renyi entropy (strict for unequal p,q; equality at p=q). These are only arithmetic margins; no adaptive event bound is inferred.

The complete newly read source section02 contains exactly the relevant joint row-count lemma: for every fixed rho,w>0, the probability that at least rho n original rows have positive-entry counts outside [pn-wn,pn+wn] is exp(-Omega_{rho,w}(n^2)). Its proof selects rho n/3 rows with a common deviation direction. Their count sum uses independent upper-triangular Bernoulli variables with weights one or two; Hoeffding and a union bound over row sets yield the displayed superexponential estimate. This pays having a large set of typical rows. It does NOT say every row is typical.

Parent explicitly warned against discarding all configurations with even one atypical row: a narrow-tolerance single-row deviation has exponential base close to1 and can dominate f(k+1)^n. That warning is incorporated. No such single-row discard is used here.

For the source corank-one theorem, the compressibility lemma first removes a bad-tail event only at the singularity rate f(2)^n. Incompressibility then gives linearly many large kernel coordinates. The row-count lemma finds a typical one among them; the adjugate selects an invertible complementary minor and controls the inverse-column norm. The source is already paying this final one-column entropy selection. Repeating that operation without new input is not a novel mechanism.

## Exact unpaid steps

1. A retained-path width-one or width-two deletion must preserve its inverse-ratio norm controls. Restricting the maximal inverse diagonal/off-diagonal search to typical coordinates controls ratios only within that set. Coordinates outside it can have uncontrolled inverse entries. No proof here supplies the full norm bound needed by the source admissible-column counting theorem. An invertible symmetric matrix's good-good block cannot vanish when the good set is larger than half the dimension, but existence of a nonzero entry is not the quantitative global ratio condition. This is a missing argument, not an actual-bit-model counterexample.

2. Fixing all bits in an exceptional rho n-coordinate set introduces exponential cost. A principal-compression treatment would need a new uniform version of the source determinant/isotropic estimates with that many omitted coordinates and a compatible path ledger. The old one-coordinate loopless compression from r50 is not such a result. Letting rho be small does not remove the need to prove the estimates.

3. For arbitrary fixed k, a kernel can contain both compressible and incompressible directions. The source's f(2)^n discard is too large for f(k+1)^n. One needs a joint structured-subspace classification and probability bound, or an exposure mechanism combining compressed and spread directions at the exact full rate. Choosing one typical large coordinate does not solve that problem. No higher-corank compressibility lemma has been proved here.

4. The original anchor may be averaged without cost only when the conditional bound is uniform over its full row. Rare lists adapted to the previously exposed matrix cannot simply be declared one fixed homogeneous codimension-k section. Schur constraints and mutual symmetry remain joint restrictions requiring their own estimate.

Thus the attempt ends with two genuine interfaces: typical-gate norm control and the joint mixed-kernel probability. No partial corank-two theorem, narrowed bias interval, or generic-matrix substitute is nominated. No impossibility theorem for the full target is asserted.

## Additional parent author obstruction: a uniform small-radius upgrade is false

After the preceding checkpoint draft, the parent supplied the following construction and said it would write a separate derivation and controls in discovery-r71-parent. This is credited author assistance, not independent review. The following verification is author-level only.

Fix p!=1/2, m=2p-1, k>=2, and let s in {+1,-1} be the more likely sign, with probability v=max(p,1-p). In k(N+1) coordinates construct k disjointly supported rows. Row j has one coefficient 1 and N coefficients -s/(mN). Divide every row by c_N=sqrt(1+1/(m^2 N)). The rows are exactly orthonormal because their supports are disjoint and their unnormalized squared norms equal c_N^2.

For independent biased signs, the jth unnormalized coordinate equals epsilon_j - (s/(mN)) sum_{a=1}^N epsilon_{ja}. The second term has mean s and variance (1-m^2)/(m^2 N). It converges in probability to s. Since c_N tends to1, the whole vector converges in distribution to (epsilon_1-s,...,epsilon_k-s), supported on vectors whose nonzero norms are at least2. Therefore, for every fixed 0<r<2,

lim_{N->infinity} P(||A_N epsilon||_2 <= r) = v^k.

The boundary sphere has no limiting mass at these r, so convergence in distribution gives this exact limit. For p=.1 and k=2 it is .81, strictly greater than p^3+q^3=.73. Thus no positive radius depending only on p,k can extend the exact homogeneous section estimate to every orthonormal-row matrix at the same f(k+1) bound. More generally v^k>v^(k+1)+(1-v)^(k+1) for v>1/2 and k>=1, since the difference is (1-v)(v^k-(1-v)^k)>0.

This does not refute the desired symmetric random-matrix corank rate, whose random kernel geometry could exclude these matrices with additional probability. It specifically blocks a dimension-free exact-to-small-ball transfer, such as importing the r68 bound directly into the JSS approximate-kernel net argument. The fair-sign case is excluded from the construction because m=0. There is no new nominee and no finite controls are claimed run here; the parent separately owns its controls.
