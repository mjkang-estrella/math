# Uncredited ordinary proof retained for separate review: 341524

This is a full all-N derivation of primary Conjecture 1 (Eq. 33), conditional on the source's established radial density (29) and its established selection-event characterization (30)-(31). It is not a proposed credited discovery, manuscript, formal certificate, or independent review. It appears to be a routine application of uniform order statistics and gamma integrals. No worldwide or bounded-registry novelty clearance is claimed.

Primary: di Pietro, Merluzzi, Calvanese Strinati, Barbarossa, *Resilient Design of 5G Mobile-Edge Computing Over Intermittent mmWave Links*, arXiv:1901.01894v3, Section IV, printed pp. 19-21, Eq. (29)-(33). Exact PDF URL, UTC retrieval, version and pre-extraction SHA256 are in current-body-provenance.json. The current arXiv abstract page lists v3; v1 also inspected. Both retain Conjecture 1. Literal extracted statement is in primary-excerpts.txt; source PDF retained. The paper's N* counts power-optimal simultaneous communication links, not transmissions or retransmissions.

Exact scope: every intensity lambda>0, path-loss exponent alpha>0, R_min>0, A=2^(R_min/alpha)>1, and every integer N>=1, in the homogeneous planar Poisson access-point model with gains proportional to d_i^(-alpha),

    P(N*=N) = exp(-a) a^(N-1)/(N-1)!,   a=2 log A.

Source input: distances d_1<d_2<... have ordered joint density

    (2 lambda pi)^N (x_1 ... x_N) exp(-lambda pi x_N^2),

and {N*>=N}=E_N={d_N^(N-1)<A product_{i<N} d_i} for N>=2, with E_1 the sure event. The event equivalence uses Corollary 1 from the optimization part of the paper; that optimization proof was not audited in full in this screen. The radial density also follows directly by mapping radius to enclosed area: T_i=lambda pi d_i^2 are successive arrival times of a rate-one Poisson process, with density exp(-t_N) on 0<t_1<...<t_N.

Proof: Integrating this last joint density in its first N-1 coordinates gives the density s^(N-1) exp(-s)/(N-1)! for T_N=s. Dividing yields conditional density (N-1)!/s^(N-1) on the ordered simplex. Consequently the ordered ratios T_i/T_N, i<N, have the law of the order statistics of N-1 independent Uniform(0,1) variables. The product is symmetric, so ordering does not affect its law. Rewriting E_N in the T variables gives

    E_N = {sum_{i<N} -log(T_i/T_N) < 2 log A}.

For independent uniforms U_i, Y_i=-log U_i has density exp(-y), y>0. Their sum of k=N-1 terms has density exp(-y)y^(k-1)/(k-1)! for k>=1: the k=1 case is immediate, and convolution with exp(-y) integrates y^(k-1) over (0,z), giving the k+1 formula. Therefore, for N>=2,

    P(E_N)=F_{N-1}(a),
    F_k(a)=1-exp(-a) sum_{j=0}^{k-1} a^j/j!.

The last equality follows by integration by parts, or induction on k starting at F_1(a)=1-exp(-a). Set F_0(a)=1 for a>0 to cover E_1. Since E_{N+1} is contained in E_N, the source event characterization gives

    P(N*=N)=P(E_N)-P(E_{N+1})
            =F_{N-1}(a)-F_N(a)
            =exp(-a) a^(N-1)/(N-1)!.

Strict versus weak inequalities have probability zero for N>=2 by the continuous gamma density; E_1 is sure since A>1. No assertion of independence between events E_N is needed. To check finiteness without circularity, if S_k is a sum of k independent Exp(1) variables, Markov applied to exp(-S_k) gives P(S_k<a)<=exp(a)2^(-k), which tends to zero. Thus N* is finite almost surely. The masses sum to one by the exponential series. This proves the full distribution for all N and all admissible continuous parameters, rather than a finite-instance statement.

Moments: the law gives E[N*]=1+a and Var(N*)=a. The source's displayed claim Var(N*)=1+a is a typo; correcting it earns no credit. The distribution derivation above is separate from that typo.

Decisive calculation: conditional uniform order statistics reduce the event exactly to a gamma CDF. bounded-checks.json additionally checks the rational polynomial difference identity for N=1..32; this verifies arithmetic implementation only. The analytical induction above, not that finite check, proves the universal formula.

Closest prior applicability: this is the generic uniform-product/gamma identity, not a new distributional principle. Its application to (29)-(31) is immediate once conditioning on the outermost radius is used. The source proves N=1,2 in Lemma 3, and our method does not change its model. We have not read a separate classical order-statistics reference or a complete successor/citing-paper census. Current v3 retains the conjecture, which does not certify novelty. Search retrievals carried Bing proof-of-work script markers; no search results are used as novelty evidence and the endpoint is now stopped. No current public proof registry checked; no acceptance or priority claim is made.

Certificate estimate and burden: approximately one to two pages of ordinary mathematical argument after the two source inputs. A literal Lean endpoint would need Poisson radial arrival laws, conditional uniform order-statistic/product distribution, gamma integration, event measurability and source optimization equivalence. That is substantial probability infrastructure; no Lean work performed and no line-count promise made.

Objections for a separate reviewer: (1) verify Corollary 1 and the exact N* selection criterion against the original power-optimization model; (2) check the conditional density and product transformation; (3) retain A>1 and lambda>0; (4) distinguish simultaneous links from retransmissions; (5) check successors and public registries before any investment, though routine-adaptation exclusion already bars discovery credit; (6) do not count the corrected variance or this standard gamma calculation as a new family. No delegate should be assigned solely for credit under the current rules.
