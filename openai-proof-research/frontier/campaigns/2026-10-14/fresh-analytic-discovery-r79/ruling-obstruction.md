# A ruling obstruction to unchanged elliptic capacity propagation

Author research only. This is an obstruction to a proposed extension of a source theorem, not an objection to that theorem under its stated ellipticity hypotheses. It is not a full-target nominee.

## Exact interface

Write A for the pinned `Diagonal-Fourier-extension-for-positively-curved-surfaces-in-three-dimensions-September-24-2026`, and B for its pinned `Elliptic-capacity-propagation-and-Fourier-restriction-to-the-sphere-September-24-2026` companion. A, section 02, equations `eq:packet-capacity`, `eq:packet-synthesis`, `eq:packet-samples`, and `eq:packet-bound`, assert for their fixed elliptic continuation phase

\[
 N^{-6}\sum|c_{\nu',z',j}|^3
 \le P(\kappa,\eta)N^{10\kappa+\eta}
 \left(N^{-2}\sum|d_{\nu,z}|^2\right)K_\kappa(d)^{1/2}.
\]

The proposed operation would replace that phase by \(\phi(\xi,\eta)=\xi\eta\) with the same arrays, gauges, and powers. The resulting assertion is false. The obstruction already uses bounded input and output labels and the single step m=N. It does not disprove hyperbolic diagonal restriction for p>3.

## Windows and arrays

Choose once and for all a source-admissible nonnegative smooth square window \(\chi\), with square-translate partition \(\sum_{k\in\mathbb Z^2}\chi(\cdot-k)^2=1\), positive near zero. Such a window is explicitly allowed in A, section 01. Choose the fixed Fourier square side D large enough that its support is strictly inside \((-D/2,D/2)^2\). Increasing this fixed side preserves the frame convention. Let \(I=[a,b]\) be a small interval about zero on which \(\chi(\xi,0)>c_0>0\).

For dyadic N, set
\[
 \nu_i=(i/N,0),\qquad z_l=(0,l/(DN)),
 \quad i/N\in I,\quad -N\le l\le N,
 \qquad d_{\nu_i,z_l}=1,
\]
and set every other coefficient to zero. These are exactly the permitted input grids. There are \(\asymp N^2\) coefficients, so \(m(d)=N^{-2}\sum|d|^2\asymp1\).

The velocities are \(U_{\nu_i}=(0,-i/N)\); both velocity and position labels occupy a bounded segment of the same vertical line. For an ellipse with axes L≥a≥1/N, each translated ellipse contains at most \(C\min(N,1+NL)\) labels of either type. The translations are independent, exactly as required by the source definition. Consequently
\[
 K_\kappa(d)\le C\sup_{L\ge a\ge N^{-1}}
 \frac{\min(1,L)^2}{L^{1+\kappa}a^{1-\kappa}}
 \le C_\kappa N^{1-\kappa}.
\]
Here L≥1/N absorbs the additive one. For L≤1 the remaining factor is \(L^{1-\kappa}\le1\); for L≥1 it is \(L^{-1-\kappa}\le1\). This upper bound holds for all orientations, not merely vertical ellipses.

## Uniform sample lower bound

Retain only output frequency \(\nu'=0\), physical x=0, physical y on the grid \(D^{-1}\mathbb Z\cap[0,cN^2]\), and integer time \(0\le j\le cN^2\), where c>0 is fixed sufficiently small. Output positions are \(z'=(0,y/N^2)\), hence are permitted and bounded. There are \(\asymp N^4\) retained samples. Their coefficient is
\[
 c(0,y,j)=\frac{N^2}{D^2}\sum_i\int\!\int
 \chi(N\xi-i,N\eta)\chi(\xi,\eta)
 \sum_{l=-N}^N e(-Nl\eta/D)
 e((y+j\xi)\eta)\,d\eta\,d\xi.
\]

Put v=Nη and \(q=(y+j\xi)/N\). For each i,ξ define
\(h_{i,\xi,N}(v)=\chi(N\xi-i,v)\chi(\xi,v/N)\).
On its support all v-derivatives have bounds uniform in i,ξ,N. Moreover its support lies strictly inside \((-D/2,D/2)\). With Fourier convention \(\widehat h(s)=\int h(v)e(-sv)dv\), Poisson summation gives
\[
 \sum_{l\in\mathbb Z}\widehat h(l/D-q)
 =D\sum_{k\in\mathbb Z}h(Dk)e(Dkq)=Dh(0).
\]
The ξ-supports lie in a fixed compact interval. Choose c so that \(|q|\le N/(2D)\) throughout the selected y,j region and all such supports. Uniform Schwartz decay then gives, for every fixed A>1,
\[
 \sum_{|l|>N}|\widehat h(l/D-q)|\le C_A N^{1-A}.
\]
After integration in ξ, the sum of lengths of the i-supports is O(1). Thus
\[
 c(0,y,j)=\frac ND\sum_i\int
       \chi(N\xi-i,0)\chi(\xi,0)d\xi+O_A(N^{2-A}).
\]
The leading integral is bounded below by a positive constant independent of N: use the positivity of χ near zero for each of the \(\asymp N\) i-values strictly inside I and integrate over a fixed multiple of 1/N about i/N. Nonnegativity prevents cancellation. With A=4, all sufficiently large N therefore satisfy \(|c(0,y,j)|\ge c_1N\), uniformly over the retained sample set.

It follows that
\[
 N^{-6}\sum_{\rm retained}|c|^3\ge c_2N.
\]
The proposed unchanged bound would instead give at most
\[
 C_{\kappa,\eta}N^{10\kappa+\eta+(1-\kappa)/2}
 =C_{\kappa,\eta}N^{1/2+(19/2)\kappa+\eta}.
\]
For example κ=η=1/100 makes this exponent 121/200<1. No scale-independent constant can reconcile the two. All windows, label regions, and loss parameters were fixed before N varied.

## What this settles and leaves open

The atomic version cannot repair this particular transplantation: the source controls the cubic sample sum by the output atomic norm, while its claimed propagation bound is no larger than the input gauge used above. Any identical atomic theorem would imply the contradicted displayed sample bound.

The source's positive-definite phase insertion also cannot produce this phase: the Hessian signature is invariant under real invertible coordinate congruence. More generally, Gaussian-curvature sign of a graph is preserved under invertible affine ambient transformations. This is a second, elementary barrier to simply inserting a hyperbolic graph into its elliptic continuation class.

The full hyperbolic restriction target remains untouched. In particular, the construction does not compare the extension norm against the original Lp norm in a way that contradicts restriction. A different capacity that charges aligned rulings more heavily, or a broad-only bilinear propagation estimate plus two-direction strip induction, could evade the obstruction. No such full estimate is proved here.

## Closest actually read primary comparison

Demeter–Wu, arXiv:2505.09037v2 (14 April 2026), Theorems 1.6 and 1.10, give bilinear decoupling for frequency squares separated in both coordinates. Their Theorem 1.11 proves restriction for p>22/7. Section 4.2, Proposition 4.11, explicitly separates horizontal and vertical strips from a transverse broad part. The array above has all frequency centers on one coordinate ruling and is therefore excluded from their transverse bilinear input. Their primary already identifies linear-subspace interference as the failure of linear elliptic decoupling; no novelty is claimed for that phenomenon. The new work in this note is only the explicit test of the pinned source's particular capacity and full sample inequality.

The precise unresolved operation is to derive a broad hyperbolic capacity propagation bound from the pinned geometric propagation and that transverse bilinear input, with losses compatible with closing both strip rescalings for every p>3. Merely replacing the source's fourth-power lemma by a bilinear theorem does not establish that operation, because the source acts on arbitrary arrays and uses a linear output norm. The current reading does not prove that no such modified route exists.
