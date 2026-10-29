# 632. Classifying Costas polynomials over extension fields

**Area:** Finite-field signal design

**Status:** 🟡 PARTIAL

**Last checked:** 2026-09-24

## Problem statement

Let $`q=p^r`$, where $`p`$ is prime and $`r\ge2`$. Suppose $`f:\mathbb F_q\to\mathbb F_q`$ satisfies $`f(0)=0`$ and, for every $`d\in\mathbb F_q\setminus\{1\}`$, the map

```math
x\longmapsto f(dx)-f(x)
```

is a permutation of $`\mathbb F_q`$. Must there exist a positive integer $`s`$ with $`\gcd(s,q-1)=1`$ and an invertible $`\mathbb F_p`$-linear map $`L:\mathbb F_q\to\mathbb F_q`$ such that

```math
f(x)=L(x^s)\qquad\text{for every }x\in\mathbb F_q?
```

Equivalently, representing functions by polynomials modulo $`x^q-x`$, must every Costas polynomial be a permutation monomial followed by a linearized permutation polynomial $`L(x)=\sum_{j=0}^{r-1}a_jx^{p^j}`$?

## Application

Costas polynomials generate circular correlation patterns over finite fields and complete families of mutually orthogonal Latin squares. A classification would determine whether the standard finite-field construction exhausts these signal and experimental-design structures.

## References

1. A. Muratović-Ribić, A. Pott, D. Thomson, and Q. Wang, [On the characterization of a semi-multiplicative analogue of planar functions over finite fields](https://people.math.carleton.ca/~dthomson/Research/pdfs/DThomson-Costas-Polys.pdf), *Topics in Finite Fields*, Contemporary Mathematics **632** (2015), 317–326, Corollary 4.2 and Conjecture 4.4.
2. I. Rubio and J. Torres, [Circular Costas maps: a multidimensional analog of circular Costas sequences](https://arxiv.org/abs/2210.16661), *Cryptography and Communications* **15** (2023), 941–958, Remark 30 and Theorem 38.
3. A. Muratović-Ribić and A. Balašev-Samarski, [Note on the Equivalence of Costas Polynomials and Orthomorphisms](https://arxiv.org/abs/2606.07097), 2026, Sections 1–3.

## Status review

**Known cases:** The analogous prime-field classification is proved. The 2026 source reports exhaustive computational verification for field orders at most 30. The proposed classification also holds under the stronger shifting condition that, for each $`d\ne1`$, there is $`a\ne0`$ with $`f(dx)-f(x)=f(ax)`$ for all $`x`$.

**Remaining target:** Establish the classification over arbitrary nontrivial extension fields without the shifting hypothesis, or construct a counterexample.

The June 2026 paper retains the conjecture and gives an equivalent orthomorphism formulation. Its enumeration repository supplies computational code, not a general proof. Current web, arXiv, GitHub, Zenodo and Palomar checks found no matching full-scope solution announcement.
