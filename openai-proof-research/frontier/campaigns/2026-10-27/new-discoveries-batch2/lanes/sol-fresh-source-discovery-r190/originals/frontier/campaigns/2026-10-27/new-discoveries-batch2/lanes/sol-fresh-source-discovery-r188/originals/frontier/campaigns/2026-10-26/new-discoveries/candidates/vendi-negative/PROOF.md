# Complete argument

Let J index the positive eigenvalues λj of the actual real PSD similarity matrix Z, retaining multiplicity. In an orthonormal eigenbasis vj, define uij=vj(i)² and wij=λj uij. Spectral decomposition gives ΣJ wij=Zii=1, ΣJ wij λj=(Z²)ii=Ei, and Σi uij=1. The diagonal1 ensures Ei≥1 and J nonempty. Symmetry and 0≤Zij≤1 give Ei=ΣjZij²≤ΣjZij=Ri, with Ri≥1.

For q<1, t^(q−1) is convex on positive reals. Jensen at each row yields Ei^(q−1)≤ΣJ wij λj^(q−1)=ΣJ λj^q uij. Summing rows gives ΣiEi^(q−1)≤ΣJ λj^q. Since q−1<0 and Ei≤Ri, Ei^(q−1)≥Ri^(q−1). This proves the energy and row bound without invertibility, including singular matrices.

The exact normalized VS interior is ΣJ(λj/N)^q=N^(−q)ΣJλj^q. The uniform LCR interior is (1/N)Σi(Ri/N)^(q−1)=N^(−q)ΣiRi^(q−1). Both share a positive factor. The exponent1/(1−q) is positive, so taking that power preserves the inequality. This proves all finite q<0 at arbitrary rank. The overlap0≤q<1 is known and uncredited.

For the canonical minus-infinity endpoint, let m=minJ λj>0 and r=min_iRi≥1. Each Ei is a convex combination of positive eigenvalues, so m≤Ei≤Ri for every i. Thus m≤r and N/r≤N/m, the exact endpoint comparison. The formal result defines these endpoints directly and does not include an analytic q→−∞ limit theorem.

VendiJensen proves the finite coupling inequalities; VendiMatrix extracts the coupling from Mathlib's canonical spectral theorem and proves all diagonal/square/column identities; VendiScores proves actual source definitions, cardinality positivity, rescaling, attained minima and both final endpoints. All assumptions are the intended finite source hypotheses. No weight, eigenbasis or normalization bridge remains as a hypothesis.
