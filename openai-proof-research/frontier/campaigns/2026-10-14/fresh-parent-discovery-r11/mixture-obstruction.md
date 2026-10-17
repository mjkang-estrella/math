# Why positivity of two mixtures does not replace a single evaluation

Myeongjin Kang, 2026-10-17. Original prose CC BY 4.0. This is a method obstruction for an attempted extension, not a new campaign nominee and not a criticism of the stipulated source theorem.

The pinned `multiscale.tex` balanced-product argument assumes a difference between one positive moment functional and evaluation at a single word, with a prescribed first wrong bit. Replacing this by the difference of two arbitrary positive probability laws is false even for an order-one feature. The following example keeps the source's Gaussian window and quantitative scale parameters. It does **not** satisfy the source's wrong-prefix hypothesis.

Let M be a sufficiently large even integer and n=M+1. For 0≤j≤M, let x^(j) be the length-n binary word with a single one in position j+1. Define probability laws μ_even and μ_odd by assigning mass

    2^(1−M) binom(M,j)

to x^(j) for j of the indicated parity, and zero otherwise. Both are positive functionals of every available degree. Let Δ=μ_even−μ_odd and choose f_(j+1)=X_(j+1), d=1. Thus the coefficient height is1, and for any complex z,

    Δ[Σ_(j=0)^M X_(j+1) z^j] = 2^(1−M)(1−z)^M.             (1)

Choose the initial scale and signal parameters

    S=s=1, ω=0, E=2M, S'=exp(−sqrt(M)).

The initial signal has magnitude 2[(1−e^(−1))/2]^M ≥ e^(−2M). The last bound follows from e>2 and log4<2. For any fixed constants C0, η0>0 in the scale-step hypotheses, all sufficiently large M satisfy S'≤η0 S and

    E ≥ C0[1+log2+log(1/S')].

The degree requirement 4k≤D is met with k=1 and D≥4. There are no inner-gap parameters.

Now fix the window constants K≥1 and 0<β<1 and set

    σ = K sqrt(E)/S',  b=βS',
    A(t) = Σ_(j=0)^M X_(j+1) exp(−j²/(2σ²)) exp(itj).

At x^(j), A(t) equals exp(−j²/(2σ²))exp(itj). A product G of r factors, each A(t) or its conjugate, with 1≤r≤4 and total signed frequency Ω, therefore evaluates to

    G(x^(j)) = exp(−rj²/(2σ²))exp(iΩj).

Let V be a centered real Gaussian of variance r/σ². Its characteristic function and (1) give the exact identity

    Δ[G] = 2^(1−M) E[(1−exp(i(Ω+V)))^M].                   (2)

For |Ω|≤b, use |1−e^(iu)|≤|u| and |u+v|^M≤2^(M−1)(|u|^M+|v|^M). Since M is even, the Gaussian moment satisfies

    E|V|^M = (r/σ²)^(M/2) (M−1)!! ≤ (sqrt(rM)/σ)^M.

Consequently every such balanced product obeys

    |Δ[G]| ≤ b^M + (sqrt(rM)/σ)^M
           ≤ [1+2^(M/2)] exp(−M^(3/2)).                   (3)

For all sufficiently large M, the right side is strictly smaller than exp(−7.94E)=exp(−15.88M). The bound holds for every choice of individual frequencies, in particular for the bounded frequencies permitted in the source argument. Thus no balanced product of at most four factors can supply its claimed threshold for this replacement class, despite the initial signal and the other quantitative parameters above.

There is no conflict with the source: Δ[X_1]=2^(1−M), not a unit wrong-bit discrepancy, and neither baseline law is evaluation at one word. In fact all x^(j) lie in the same cyclic orbit, and these two parity-binomial laws are not uniform rotation-invariant orbit measures. This example does **not** disprove circular trace reconstruction, nor separation of two distinct uniform orbits. It does show that positivity and a nonzero initial signal alone cannot pay the proposed mixture version of the Gaussian balanced-product step. A successful circular argument must use additional orbit structure or a different observable conditioning mechanism.

No numerical evidence is needed for (1)–(3): the binomial theorem, Gaussian characteristic function and explicit even moments prove them. This is an author calculation, not an independently reviewed acceptance. Reading provenance and the separate exact channel calculation remain in screen.md and its receipts.
