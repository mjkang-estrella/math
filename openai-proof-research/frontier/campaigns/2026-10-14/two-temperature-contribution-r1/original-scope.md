# Frozen target R2T: two radial temperature transitions on one density interval

Myeongjin Kang; no affiliation. Original prose CC BY4.0; original code MIT. Third-party sources retain their rights. Discovery author statement, not independent acceptance.

Let p=lim_{L→infinity} M_L/L^3, where M_L is the largest size of a1-separated subset of [0,L]^3 in Euclidean R^3.

Prove existence of ONE bounded continuous radial pair potential phi:[0,infinity)→R, finite constants B,C>0, eta>0 with eta<2p, and TWO inverse temperatures

beta_1 in (31/32,33/32), beta_2 in (41/32,43/32),

such that the following all hold.

1. For every integer N>=0 and every configuration x_1,...,x_N in R^3, including coincidences, sum_{i<j}phi(|x_i-x_j|)>=-BN.
2. For every r>=1, |phi(r)|<=C r^(-3-1/32).
3. Define Z_{L,N}(beta)=(1/N!) integral_{[0,L]^(3N)} exp[-beta sum_{i<j}phi(|x_i-x_j|)] dx, with Z_{L,0}=1 and ordinary beta-independent Lebesgue position measure. For every beta>0 and rho>0, the limit f(beta,rho)=-lim_{L→infinity}(beta L^3)^(-1)log Z_{L,floor(rho L^3)}(beta) exists and is finite.
4. For EVERY rho in the SAME interval I=(2p-eta,2p+eta), and BOTH j=1,2, the one-sided beta derivatives at beta_j are finite and satisfy f'_-(beta_j,rho)>f'_+(beta_j,rho).

The potential, density interval and both temperatures are common to all rho; beta_1 and beta_2 are distinct by their disjoint windows. The conclusion is at least two transitions, not exactly two; no conventional liquid/solid/vapor phase identification, finite-range claim, Gibbs-state classification or prescribed numerical transition temperatures is asserted.

Source premises are stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Every new deduction must be proved. If unresolved, this whole scope remains unresolved; a four-plane convex picture, separately tuned potentials, or only distinct-density Gibbs coexistence cannot substitute for item4.
