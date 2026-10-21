# Integrated Source215 / Hepp reduction

PREFREEZE / no nominee. These are feasibility notes reconstructing the strongest compatible source/classical operation examined, not a frozen author theorem or an independent grade. P denotes the pinned isolated-pole paper; C the pinned canonical-continuum paper; H Hepp1965, pp95–111. All source operative proofs are stipulated true.

## 1. Keep the field and units fixed

Use the prescribed C Theorem1.2 field phi=(phi^1,phi^2,phi^3), with a_N=L^-N and the same B_N as in P inputs. It is a local Hermitian scalar multiplet in1+1 dimensions with positive Hilbert space, Poincare covariance, unique vacuum, full positive Hamiltonian gap, and tempered Wightman distributions. These are the hypotheses actually proved in C os.tex, not inferences from the title.

P intro:main supplies m1>0, Z>0, delta>0 and

  W2^{ij}=delta_ij [Z Delta_+(m1²) + integral Delta_+(mu²) rho_rest(dmu²)],
  supp rho_rest subset [(m1+delta)²,infinity).

There is no vacuum atom because internal inversion makes phi odd. Choose a fixed open mass-squared strip |p²-m1²|<c, with 0<c<min(m1², (m1+delta)²-m1²), in the positive energy cone. Normalize A^i=Z^-1/2 phi^i. Compactly supported smooth Fourier tests in this strip create only the one-particle spin subspace from vacuum, exactly as in H(2.1)–(2.3). The normalizations are fixed once, not at each scattering time.

The resulting one-particle space is

  h_spin = L²(R, dp/(2pi 2omega(p))) tensor C³,
  omega(p)=sqrt(p²+m1²).

The isometry into H follows directly from W2, with the three components orthogonal. This describes the spin-visible triplet; it does not assert that all particles or all degenerate species in H have been classified.

C canonical normalization is one fixed positive dilation of spacetime and one fixed positive field rescaling. Such a dilation changes m1 and wavepacket arguments by reciprocal units; multiplying phi changes Z by its square and cancels in Z^-1/2 phi. Existence/nonexistence of a nonzero transition matrix element is invariant under this unitary change of units. No identification of different lattice actions or theta terms is made.

## 2. Why the bounded-operator issue is already paid

Dybalski0412226v4 gives a useful stronger general theorem for possibly embedded masses, but its regularity condition A' is imposed on bounded local operators A. Passing from phi's two-point gap to a bounded function of phi need not preserve a vacuum spectral gap. It would be wrong simply to insert that bounded function and declare A' automatic.

H's actual Wightman-field proof avoids this detour. It starts from the field two-point strip. For a positive-frequency test f, write A_t(f) for H's spacetime-smeared creation operator with phase exp(i(p0-omega(p))t). It maps the common polynomial domain into itself; A_t(f)Omega is independent of t, and its adjoint annihilates Omega. All higher products are interpreted on that domain.

For n packets with pairwise disjoint velocity supports within this one family, expand the squared norm of

  d/dt [A_t^{i1}(f1)...A_t^{in}(fn)Omega]

into products of truncated Wightman distributions. Terms consisting only of one/two-point blocks vanish: the derivative of a one-particle vacuum vector is zero, and the vacuum expectation of a single field vanishes. Every surviving contribution contains a truncated block of size at least3. Massive spacelike clustering gives smooth spatial Fourier kernels after energy smearing, with polynomial derivative bounds. Compact momentum supports and disjoint velocities make a phase derivative nonzero, so repeated integration by parts pays every inverse power of |t|. Finite component indices only produce a finite sum; no new spin statistics or spacetime spin issue is introduced.

Concretely, in H(2.10)–(2.14) the relevant derivative is a difference of the two wavepacket velocities (with the total-momentum sign convention already included). On the compact support its absolute value has a positive lower bound. In one spatial dimension there is one derivative direction; there is no need for the three-coordinate partition in the displayed4D proof. H p98 expressly records that the rapid-convergence argument is independent of the spatial dimension, including one dimension.

For every fixed packet family and every M there is C_M<infinity such that the differentiated vector norm is <=C_M(1+|t|)^-M. Cook integration gives both limits. There is no uniform claim as the velocity separation tends to zero.

H pp99–100 also pays the unbounded-operator domain passage: multiplying the derivative by a fixed polynomial B is controlled by Cauchy–Schwarz; one factor decays arbitrarily fast and the other grows only polynomially by temperedness. Hence the limit lies in the closures' common domain and products/locality pass to the scattering domain. No bounded truncation spectral premise is smuggled in.

These are actual classical proof operations. The earlier thought of needing a global mass-isolation upgrade is unnecessary for this Wightman construction. The independent source full gap supplies the massive clustering hypothesis; it need not equal m1 for this use. The boost-mixture calculation in ALL-STATE-TRANSFER subsequently pays full mass isolation as well. It is not an additional nominee; it supplies the stronger spectral reading of SectionIII if required.

## 3. Fock maps and precise limits of what they say

The same-side inner products have the bosonic permanent form

  <W_±(h1 tensor_s ... tensor_s hn), W_±(g1 tensor_s ... tensor_s gn)>
     = sum_{pi in S_n} product_j <hj,g_pi(j)>,

with h1 tensor_s ... tensor_s hn defined as (n!)^-1/2 times the sum of the n! ordinary tensor products. This fixes the permanent normalization. Different particle numbers are orthogonal. Disjoint-support smooth packets are dense: partition momentum into small intervals, discard the coincidence diagonals of Lebesgue measure zero, then approximate. Finite color sums are dense in the internal triplet factors. Thus W_± extend to isometries Gamma_s(h_spin)->H. The maps intertwine translations, boosts and internal O(3) transformations, by uniqueness/field independence of the packet limits and the underlying covariance.

This is the source/Haag–Ruelle/Hepp composition. It is not a substantial nominee here. Define T=W_+*W_- as the incoming-to-outgoing transition operator on the spin Fock space. It is a contraction. Without equality of the in/out ranges it is not asserted unitary, and no asymptotic completeness is claimed. Nontrivial scattering would mean an actual packet matrix element different from the free bosonic inner product, not merely existence of W_±.

## 4. The strongest LSZ bridge, including the1+1 elastic issue

H SectionIII explicitly refers to a mass eigenvalue outside the continuum. ALL-STATE-TRANSFER pays this stronger full-spectrum interface from the actual source counting proof, rather than silently substituting field-only isolation. H first regularizes time ordering, proves rapid large-time bounds, and derives the smooth amputated boundary restriction for all-leg nonoverlapping velocities. Its full proof, not just the theorem heading, was read. Crucially H p111 states repeated mass-shell reduction for separately nonoverlapping incoming and outgoing momenta, independent of the order. The all-leg condition is therefore not a retained obstacle.

For incoming h1,h2 of separated velocities and outgoing g1,g2 separately separated, the connected transition is

  D(g1,g2;h1,h2)
   = <W_+(g1 tensor_s g2),W_-(h1 tensor_s h2)>
     - sum_{pi in S2} product_j <gj,h_pi(j)>.

H identifies this, with his fixed Fourier factors, with the iterated four-leg amputated, on-shell connected time-ordered distribution. Schematically it is the packet pairing of

  Z^-2 [product_{j=1}^4(p_j²-m1²)] G4_connected

at the appropriate positive/negative energy shells. The displayed expression is schematic about Fourier i and2pi factors; the invariant packet definition of D above is exact. No nonzero value is claimed from a schematic normalization.

In1+1 equal-mass elastic kinematics the unordered outgoing momentum pair equals the unordered incoming pair. At fixed total spatial momentum P, E_P(p)=omega(p)+omega(P-p) is strictly convex, symmetric about P/2 and strictly monotone on each side, since omega''(p)=m1²/(p²+m1²)^(3/2)>0. Hence E_P(p')=E_P(p) gives p'=p or P-p. Requiring all four packet velocity supports disjoint would therefore miss the elastic channel. Separately nonoverlapping in/out packets are the correct test, already paid by H's iterated restriction.

The source fixed-scale cumulant is nonzero before amputation. The restriction above is a different linear operation, with a large kernel. Neither analyticity of a nonzero off-shell distribution nor its sign on one collection of Euclidean tests forces its restriction to a lower-dimensional mass-shell set to be nonzero. The quantitative source construction must be carried through that projection to close D!=0; that operation was not obtained.

## 5. What the exact source-source proof does and does not supply here

C os.tex proves the actual terminal-cell cumulant -2/15+o_H(1): four nearby fixed cells share nearly aligned terminal spins, whose one-component second/fourth moments are1/3 and1/5. Source comparison, moment convergence and shrinking boundary strips then give nonzero smooth separated-time tests. It does not compare this cumulant to the one-particle-projected external legs.

C sources.tex's complete source-step proof was read. Its coefficient majorants retain all source degrees; degree>=2 terms contract through l² anchor choices times l^-2a, and degree1 terms use alignment subtraction and a C/L contraction. Nonlinear/exceptional terms are controlled by absolute majorants. The endpoint comparison is at fixed bottom layer and fixed period. These estimates pay construction and moment comparison; they are upper estimates and fixed-scale limits, not a signed lower bound on D after mass-shell amputation. Failure of this attempted application is not an audit of the stipulated proof.

The Wick-field diagnostic in DIAGNOSTICS shows concretely why the qualitative two-point pole plus nonzero negative four-cumulant interface cannot by itself prove D!=0. It is not a model of the entire pinned lattice/RG construction and does not exclude a stronger source-specific calculation.

Conclusion of these feasibility calculations: scattering-state existence and the relevant iterated reduction are paid classical compositions. No additional closed nonroutine operation producing nonzero D has been identified. No theorem is frozen, no proof nominee is submitted, and no independent grade or campaign count is assigned.
