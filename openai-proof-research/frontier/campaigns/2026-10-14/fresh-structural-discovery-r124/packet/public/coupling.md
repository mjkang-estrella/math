# Source231: the actual response contract

No target was frozen. The general ordered determinantal coupling direction was already explored in structuralr64/r106; r18 and analyticr121 already contain the canonical covariance-graph sampling construction. This round does not restart any of those scopes or nominate an equal-marginal special case.

The source `prop:brownian-sampler` in decoder.tex is not restricted to strongly Rayleigh (SR) laws. For a probability law on a countable binary product, it accepts a single finite L bounding the sup-norm Lipschitz constants of ALL selected finite-tilt means, uniformly in site, exhaustion index and time. `lem:inverse` then uses Picard iteration with factorial error, on the full product path space including unbounded coordinate inputs. The reference observation law, innovations, deterministic uniqueness and integer-time slopes give the full sampled law. Equivariance must hold for the chosen drift/exhaustions; it does not automatically hold for every action from an arbitrary enumeration.

Source `lem:sr-response` is one sufficient input: at every finite external-field tilt, the absolute covariance row sum is at most2 Var(X_i)<=1/2. Symmetric homogenization, dummy variables and nonpositive off-diagonal covariances give this bound. Arbitrary finite marginals, complex Hermitian determinantal contractions and singular kernels are already included. Homogeneity, full support and trace class are not missing hypotheses to add as new results.

## Stronger check of the doubled-joining objection

An old attempted route was to seek an SR law of the complemented pair (X,1-Y) witnessing X<=Y. With equal marginals this forces X=Y almost surely, coordinate by coordinate. If X has a strictly negative off-diagonal covariance, Cov(X_i,1-X_j)>0, violating the necessary negative pair correlation of SR. This does rule out that representation as SR. It does NOT rule out the source's actual more general response contract.

Indeed let X be any SR process and set Z_(i,0)=X_i, Z_(i,1)=1-X_i. For any finite set of observed Z-coordinates, an external tilt with fields a_(i,0),a_(i,1) becomes a tilt of X with effective field

    h_i = a_(i,0)-a_(i,1),

where missing fields are zero; the additive sum of complement fields cancels in normalization. Include the tested coordinate's index in the finite X marginal. Differentiation of the finite partition function gives each derivative of a tilted mean of Z as a signed covariance of X. Each original observed index occurs at most twice. Therefore its absolute derivative row sum is at most

    2 sum_j |Cov_h(X_i,X_j)| <= 1.

This works for every finite set and arbitrary real fields, and hence also for fields y-t/2 in the source observation model. On a regular countable group with two labels per site, translated finite exhaustions supply the corresponding group equivariance, and iid per-site labels can be split into two iid inputs. The existing sampler is compatible at L=1. More simply, an existing sample X can be duplicated and complemented. This check supplies no new general theorem or contribution claim; it only prevents the false inference that failure of SR is failure of every source-compatible joining.

For arbitrary ordered positive contractions Q1<=Q2 on a countable group, the missing object remains a jointly invariant monotone law with sufficient finite-field response control, or another full construction of the desired monotone factor. Marginal response bounds do not construct a joint response bound. Independently sampling the two marginals does not impose order. Using common Brownian noise has no demonstrated comparison principle: source drifts have negative off-diagonal derivatives. This is a method limit, not nonexistence of invariant or FIID monotone couplings.

## Primary and historical comparison

Lyons–Thom, [Invariant Coupling of Determinantal Measures on Sofic Groups,1402.0969v2](https://arxiv.org/pdf/1402.0969v2), actual Theorem5.1 proof was read. Its positive-operator lift and finite sofic Schreier approximants support finite monotone couplings and averaging/limits. These operations do not drop the sofic hypothesis by merely sampling the two marginal laws. Earlier determinantal order and Strassen supply finite couplings, not an invariant choice on an arbitrary group. The finite-chain extension is already recorded after Corollary5.2. The complete paper and d-bar proof were not reread.

Actual analyticr18 original-scope/checkpoint already give covariance-threshold components, independent component laws, finite balls and canonical all-input naturality. Analyticr121's later screen repeats the exact historical discovery and is not a new candidate. R64/r106 already identify the ordered-joining direction and the complemented-SR limitation. The present response calculation follows those actual bodies and the complete decoder/SR sections; it must not be presented as closing their full ordered-pair question. No full joined-law construction was found.
