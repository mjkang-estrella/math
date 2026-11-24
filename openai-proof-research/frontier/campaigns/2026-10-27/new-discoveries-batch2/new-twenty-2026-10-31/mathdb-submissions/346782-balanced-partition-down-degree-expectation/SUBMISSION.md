# MathDB 346782: The balanced-partition conjecture for the $\mathsf a;q$-down-degree expectation

- Problem: https://mathdb.com/p/346782
- Source: Jang Soo Kim, Michael J. Schlosser and Meesue Yoo, “Enumeration of standard barely set-valued tableaux of shifted shapes”, arXiv:2006.03253 (2020); Electron. J. Combin. (2023), Conjecture A.2. (https://arxiv.org/abs/2006.03253)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `BalancedPartition.ksy_conjA2`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. 'Balanced' is read as in the journal version (upper left corner of each addable cell on the line); the arXiv wording is ambiguous. Bounded literature search only; Hopkins, Lazar and Linusson remark in print that they could not connect the conjecture to their methods.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every balanced partition the a;q-down-degree expectation equals the conjectured closed form in Q(a,q). This is Conjecture A.2 of Kim, Schlosser and Yoo (arXiv:2006.03253; Electron. J. Combin. 2023). The proof is a telescoping identity over the corners of the shape. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathsf a$ and $q$ be indeterminates. For a balanced partition $\lambda$, write $w=\lambda_1$ for its width, $\ell=\ell(\lambda)$ for its length, and $d=\gcd(w,\ell)$. Define

$$
W_{\mathsf a;q}(n)=\frac{1-\mathsf a q^{1+2n}}{1-\mathsf a q}q^{-n},\qquad [n]_{\mathsf a;q}=\frac{(1-q^n)(1-\mathsf a q^n)}{(1-q)(1-\mathsf a q)}q^{1-n}.
$$

For $x,y\in[\emptyset,\lambda]$ with $y\lessdot x$, if $y$ is obtained by deleting a cell in row $s$, set

$$
\operatorname{wt}(x,y)=W_{\mathsf a q^{\frac{w+\ell}{d}};q}\left(\frac{w(s-1)+\ell(|x|-1)}{d}\right).
$$

Define

$$
\operatorname{ddeg}_{\mathsf a;q}(x)=\sum_{y\lessdot x}\operatorname{wt}(x,y),
$$

with the sum over $y\in[\emptyset,\lambda]$, and

$$
R(\lambda\mid\mathsf a;q)=\sum_{x\in[\emptyset,\lambda]}W_{\mathsf a q^{\frac{w\ell}{d}};q}\left(\frac{\ell|x|}{d}\right),
$$

so that

$$
\mathbb E_{\mathsf a;q}(X)=\frac{\sum_{x\in[\emptyset,\lambda]}\operatorname{ddeg}_{\mathsf a;q}(x)}{R(\lambda\mid\mathsf a;q)}.
$$

**Balanced-partition product conjecture.** If $\lambda$ is balanced, then

$$
\mathbb E_{\mathsf a;q}(X)=\frac{\left[\frac{w\ell}{d}\right]_{\mathsf a q^{\frac{w+\ell}{d}};q}}{\left[\frac{w+\ell}{d}\right]_{\mathsf a q^{\frac{w\ell}{d}};q}}.
$$

This is an $\mathsf a;q$-analogue of the down-degree expectation formula. The source presents it as a conjecture for balanced partitions of arbitrary slope; no resolution is supplied.

## Summary of the result

For every nonempty balanced partition (in the journal's sense: the upper left corner of each addable cell lies on the diagonal line), the a;q-weighted expectation of the down-degree statistic of Kim, Schlosser and Yoo equals the conjectured quotient of a;q-numbers, as an identity in the field of rational functions Q(a,q); the denominator is proved nonzero. This is Conjecture A.2. The proof is a telescoping corner identity. The formula fails for every unbalanced shape tested, so the hypothesis is needed.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
