# Canonical form realization: proved supporting consequence, not a nominee

All statements here are conditional on source278's displayed orbitals and weighted spectral gap. This construction uses the classical ground-state representation and Friedrichs form closure. It is a routine completion of the source certificate, not a substantial new contribution claim.

Let g>0 and h be the source real orbitals, with ||g||²=2, ||h||²=1, <g,h>=0, g,h in H1 and H2_loc, V=Delta g/(2g) in L2_loc, int n|V|<infinity, n=g²+h², and distributional equations (-Delta/2+V)g=0 and (-Delta/2+V)h=d h. The source gives, for compact smooth complex f,

q[f]=1/2 int g²|grad(f/g)|² >= d (||f||²-|<g/sqrt2,f>|²).

## Closure and the two eigenvectors

Multiplication by 1/g is unitary from L2(dx) to L2(g²dx). On each compact set, continuity and strict positivity of g bound the weight above and below. The weighted gradient form is therefore closable: if f_j→0 in L2 and weighted gradients of f_j/g are Cauchy, their limit has zero distributional pairing with every compact smooth vector field, hence is zero. Equivalently one can use the local weighted Sobolev closure. Let Q be the closure of q on C_c^infinity, and H its nonnegative self-adjoint operator. Since V is locally L2, the minimal differential operator on C_c^infinity is defined and H is its Friedrichs extension.

Compactly supported H1 functions belong to this form closure: local H1 approximation by smooth functions makes kinetic terms converge, and V in L2 on the compact support makes potential terms converge by strong L4 convergence. The source's local positive-orbital identity agrees with Q there.

For smooth cutoffs chi_R, bounded by one, equal one on B_R, zero off B_2R, |grad chi_R|<=C/R, the distributional eigen-equation yields

q[chi_R f]=epsilon ||chi_R f||² + 1/2 int |grad chi_R|² |f|²

for f=g,h and epsilon=0,d. The same identity for differences of two cutoffs shows chi_R f is Q-Cauchy: the first term tends to zero on the escaping support and the gradient term is bounded by C R^{-2}||f||². Thus g,h are in Dom Q. Passing the compact-test weak eigen-equation to the closure gives Q(g,v)=0 and Q(h,v)=d<h,v> for every v in Dom Q. Consequently g,h belong to Dom H, with Hg=0 and Hh=d h.

The spectral gap inequality extends by closure to all Dom Q. The zero eigenspace is exactly span(g), and H restricted to its orthogonal complement is at least d. (Alternatively zero weighted gradient implies f/g constant on connected R³.) There is no need to assert that Dom Q equals H1 or that the negative and positive potential energies are separately finite for every form vector.

## Exact generalized Kohn–Sham representation

On spin space H tensor identity_2 has a two-dimensional zero eigenspace and the remainder is at least d. The sum of three copies restricted to the fermionic wedge is at least d: at most two electrons can occupy the zero eigenspace, by the Pauli bound. The determinant (g/sqrt2 up) wedge (g/sqrt2 down) wedge (h up) is an eigenvector of energy d and has density g²+h²=n. Hence it is an exact ground-state representation for this Friedrichs realization.

Source278 proves V is not in L^{3/2}+L∞. No contradiction occurs: its prohibited class gives the ordinary H1 form domain and uniform form control, whereas this construction permits a strictly different closed form. The density does not become representable in the source's class. This result is not a new molecular example, a statement about arbitrary densities, or a claim that all generalized potentials enjoy the source's ensemble-transfer theorem.
