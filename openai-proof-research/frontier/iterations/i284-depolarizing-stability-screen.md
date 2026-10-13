# I284 — A prior stability theorem and a failed channel-transfer shortcut

Parent source screen, 2026-10-12. **Research lead and technical obstruction only; no accepted finding.** The full GAD stability target remains open in this record. I280 and I281 received the same primary-source lead while running; neither received the other's output.

## Primary result inspected

Bae, Gour, Lee, Park and Sanders, [Stability theorem of depolarizing channels for the minimal output quantum Renyi entropies](https://arxiv.org/abs/1510.07815), arXiv:1510.07815v1, [primary HTML](https://arxiv.org/html/1510.07815). The parent read Sections II and III through Theorem 6, including Lemma 5 and the von Neumann-entropy remark, equations (44)–(45). The paper treats depolarizing tensor powers and claims output-entropy stability toward pure product inputs. Its proof expands about a closest product state, removes weight-one perturbations and bounds the remaining quadratic coefficients. These are relevant precedent, not a GAD theorem. The displayed Taylor remainders and the passage from small perturbations to the full stability statement need their quantifiers checked before any use as a dimension-uniform black box. No assertion that this paper's theorem is false is made here. No full PDF authentication or comprehensive literature screen was performed.

This source can inform the phase-stability investigation and its eventual contribution comparison. It does not supply I273's target merely because both channels have product minimizers.

## A simple postprocessing reduction does not work

Consider the unital GAD case nu=1/2. Write s=sqrt(1-gamma), with 0<s<1. Its Bloch action is diag(s,s,s^2). Let D_s be the qubit depolarizing channel, with Bloch action diag(s,s,s). If A=D_s composed with B (or B composed with D_s), linear invertibility forces B to have action diag(1,1,s). The four Pauli coefficients of this unique map are

    (3+s)/4, (1-s)/4, (1-s)/4, (s-1)/4.

The last is negative. Thus B is not completely positive and no CPTP factorization of this form exists. This also follows from the negative corresponding Bell-basis Choi eigenvalue. One cannot transfer entropy stability by declaring this map to be an additional quantum noise channel. This calculation is an elementary obstruction, not a substantial result.

A convex decomposition is possible: put w=(1-s)/2 and define the unital Pauli channel C by Bloch action diag(s,s,c), where c=s(3s-1)/(1+s). Then A=wD_s+(1-w)C. Complete positivity follows from 1+c>=2s and 1-c>=0; the first inequality has numerator (1-s)^2. Also -s<=c<=s, so the maximum output Bloch length of C is s. The same one-site minimum entropy is therefore attained on equatorial pure states. This is only a one-site observation.

In the tensor expansion, however, the all-depolarizing term has weight w^n. Isolating that term would attach an exponentially small prefactor to its stability estimate. This decomposition alone does not provide an n-independent GAD bound. Recovering a useful estimate from the other mixed terms is separate work, not a consequence claimed here.

## Status

No new contribution or global GAD proof is nominated. The value of this screen is to credit an existing stability literature and rule out a tempting unproved reduction. Purely local Taylor coefficients, fixed-n compactness, a non-CP inverse, and an exponentially weighted all-depolarizing branch do not establish the original target. The original twelve acceptances remain unchanged.
