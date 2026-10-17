# Frozen target CS: a natural sampler for strongly Rayleigh laws

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Scope frozen after the primary-operation screen on 2026-10-16. Source truth
is stipulated at openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

For every finite or countably infinite set I, let SR(I) be the strongly
Rayleigh probability laws on {0,1}^I, with the relative Borel structure
from the space of probability laws with its weak topology. There exist
jointly Borel maps

    Phi_I : SR(I) x [0,1]^I -> {0,1}^I

such that:

1. For every nu in SR(I), Phi_I(nu,U) has the entire joint law nu when U
   has independent uniform coordinates.
2. For every bijection sigma:I->J between finite or countably infinite
   index sets, every nu in SR(I), and EVERY u in [0,1]^I,

       Phi_J(sigma_*nu, sigma u) = sigma Phi_I(nu,u).

3. Consequently, for every group acting by permutations on I and every
   invariant strongly Rayleigh law nu, Phi_I(nu,.) is an equivariant IID
   factor for that action, simultaneously for all group elements on every
   label input. Neither the group nor its stabilizers need be countable.
   No transitivity, regularity, freeness, amenability, local finiteness,
   or given graph structure on I is assumed.

The same conclusion therefore applies to every determinantal law with a
Hermitian positive-contraction kernel on l2(I), equivariantly under all
permutations preserving the LAW; invariance of a particular kernel
representative is unnecessary. Kernels need not be trace class or invertible.

The maps may use the law nu as a parameter. No finitary coding, continuity
in nu, uniform runtime, finite alphabet, monotone coupling of distinct
laws, or Bernoulli isomorphism is asserted. The theorem is not a claim
that arbitrary invariant probability laws admit such a sampler.

This complete target is one candidate, not separate findings for finite
sets, countable sets, group actions, and determinantal laws. No independent
proof/contribution verdict or campaign count is assigned here.
