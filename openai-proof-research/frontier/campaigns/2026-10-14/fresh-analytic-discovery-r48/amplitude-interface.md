# The amplitude is a different, presently unpaid interface

Myeongjin Kang. Original prose CC BY 4.0. This is a pre-freeze route analysis, not a frozen theorem or a conditional nominee.

The technical estimate in 216-technical-transfer.md bounds the critical magnetic response above and below by constant multiples of

    g(h)=h^(1/15)(log(1/h))^(1/15).

It does not prove that m(h)/g(h) has a limit, even though the source identifies finite positive amplitudes for the zero-field center magnetization and axis two-point function. Those source amplitudes are not amplitudes of the field-perturbed thermodynamic pressure.

The source spin-field theorem takes a lattice limit in one fixed square with aligned boundary and compactly supported test functions. The absolute Lee–Yang bound allows bounded-parameter exponential tilts of those fixed-domain observables. That operation is routine uniform integrability. It does not give an error uniform in the size of the continuum domain or in a tilt parameter tending to infinity. In particular, the lattice limit and the subsequent thermodynamic limit cannot simply be exchanged.

To see the needed estimate concretely, put s_n=n²a_n and h_n=t/s_n for fixed t>0. A field-pressure amplitude would require control of n²[p(h_n)−p(0)] as n→∞. A fixed box of side proportional to Rn gives a normalized tilted logarithmic partition function whose lattice limit may be identified for each fixed R after handling the boundary. One would then need an upper and lower thermodynamic sandwich with errors tending to zero as R→∞ uniformly in sufficiently large n. Ordinary bounded-interaction boundary surgery costs O((Rn)^(−1)) per lattice site. After multiplying by n², that is O(n/R), which diverges at fixed R. This elementary estimate is therefore inadequate. It is an insufficiency of that estimate, not an obstruction to the amplitude theorem.

A sufficient new operation would bound the *difference* between the field-on and field-off boundary free-energy errors at the magnetic scale by o_R(1)/n² per site, uniformly in n. Alternatively, a uniform massive-field comparison or an appropriate subadditive continuum pressure identification could serve. The source's temperature-response/mass companion changes b below b_c and studies the dual height trajectory; its introduction does not assert this external-field boundary comparison. No lower proof of that companion is claimed to exclude a hidden applicable estimate, and no exhaustive primary novelty claim is made.

Even adding regular variation and GHS-type scalar concavity to the comparison bounds would not establish the amplitude. For an exact diagnostic, let α=β=1/15, u=log(1/h), and for sufficiently small h define

    f(h)=h^α u^β [2+ε sin(log u)],       0<ε<1/2.

Then f(h)/g(h) oscillates without a limit. For every fixed t>0, f(th)/f(h)→t^α, because log(u−log t)−log u→0 and the oscillating factor stays bounded away from zero. Set A(u)=u^β[2+ε sin(log u)]. We have A'(u)/A(u)=O(1/u) and A''(u)/A(u)=O(1/u²). Direct differentiation gives

    f'(h)=h^(α−1)[αA−A'],
    f''(h)=h^(α−2)[α(α−1)A−(2α−1)A'+A''].

Thus f'>0 and f''<0 for all sufficiently small h. Its primitive is a convex pressure with zero-field derivative zero. This scalar example is not an XY Gibbs model and does not refute any magnetic amplitude statement; it only prevents an unjustified inference from comparability, regular variation and concavity.

No full-amplitude target was frozen, and no narrower replacement is proposed. The decision is to retain the proved technical transfer and this exact unmet uniformity requirement without nomination.
