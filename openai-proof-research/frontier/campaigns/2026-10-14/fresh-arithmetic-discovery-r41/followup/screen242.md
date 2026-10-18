# 242: smooth unique witnesses are a technical Poonen transfer

Prefreeze screen; no nominee. Stipulated source thm:main and cor:unique-h10 already give fixed m,D and undecidability under at most one complete N-witness. Read source main.tex lines1–190 and consequences.tex in full. No other proof in the family is claimed read.

The tempting strengthening is to require every input hypersurface over Q to be smooth and geometrically integral, retaining fixed dimension/degree and the at-most-one N-point promise. This strengthening has a complete simple transfer, but its operative construction is already Poonen's Lemma4.1. It is not substantial new mathematics.

Here is the exact uniqueness-preserving variation, with proof. Given a nonconstant integer polynomial P in m>=1 variables, choose a positive integer c for which

    F(w,y)=P(w)^2+c y(y+1)

is smooth over Q. Such c exist and can be found by testing c=1,2,... with the Jacobian criterion/ideal membership over Q. At a geometric singularity, y=-1/2, P(w)^2=c/4, and all partial derivatives of P vanish (P is nonzero there). A polynomial on affine space in characteristic zero has only finitely many critical values: on each irreducible component of its critical locus its differential vanishes, hence it is constant on that component, and there are finitely many components. Thus only finitely many c can be bad. This is the same Bertini/critical-value operation as Poonen's proof.

For N-inputs, both summands are nonnegative and y(y+1)=0 precisely at y=0. Therefore F has exactly as many N-solutions as P, with the bijection w -> (w,0). Degree is 2deg(P). Geometric integrality also follows directly: as a quadratic in y its discriminant is 1-4P^2/c. If that were a square in C[w], factoring U^2+4P^2/c=1 into two factors over C would force both to be units and P constant. The primitive monic quadratic is therefore irreducible over C[w,y]. In the fraction-field version, a rational square that is polynomial is a polynomial square by unique factorization. Thus F defines a geometrically integral hypersurface.

If a promised input P is constant, it cannot be zero since m>=1 and there would then be infinitely many N-witnesses. This decidable empty case can be sent to F0=sum(w_i^2)+y(y+1)+1: it has no N-points, is smooth (the unique critical point gives value3/4), and is geometrically integral by the same quadratic criterion, since 1-4(sum(w_i^2)+1) is not a square. Fixed m,D therefore remain fixed after transformation. No source coefficients must be effectively discovered: the source itself hard-codes one representing polynomial, and the new c-search is effective on each specialized input.

Actual closest primary: Bjorn Poonen, Automorphisms mapping a point into a subvariety, author PDF https://math.mit.edu/~poonen/papers/automorphism.pdf, Lemma4.1 and proof, Lemma4.2 and proof, Corollary4.3, §5 were read in extracted lines120–205. His polynomial is c(y^2-y)+f^2, over Z; replacing y by -y gives the displayed expression, and choosing N as the witness domain selects just y=0. His proof already supplies smoothness, geometric integrality, effectivity and bounded degree. This is a technical uniqueness bookkeeping consequence of the new source, not a new smoothing operation. The stronger smooth-projective-closure construction is also already his Lemma4.2; it is not offered as another finding.

No claim of novelty or independent proof review. The earlier thought that a sum of squares must force singularity does not apply: y(y+1) is nonnegative only on the witness domain, not globally on R, and has nonzero derivative at y=0. This corrected screen preserves that distinction.
