# Author clarification: higher contracted ideals in the primary comparison

This note changes no frozen r29 byte, theorem scope or proof. It is an author-side clarification for both independent gates, not a review verdict. Campaign count remains13/20.

## The formula-level issue

Let B be a domain, p a prime element of B, F∈B with p∤F, and suppose B embeds in

    A=B[Y]/(p^rY−F), r>=1.

For any s>r put k=ceil(s/r). Inside A,

    F^k=p^(rk)Y^k=p^s[p^(rk−s)Y^k].

Consequently F^k∈(p^sA)∩B. But p∤F^k, because p is prime. Therefore this contraction is NOT contained in pB, and in particular cannot equal

    (p^s,p^(s−r)F)B ⊂ pB.                                  (*)

This obstruction also applies with relation p^r aY=F: the same identity has a^kY^k on the right. Inverting other coefficient factors does not eliminate the missing powers of F.

An exact elementary model is B=k[p,t], F=t, r=2, s=3. Then A≅k[p,Y] under t=p²Y, and

    (p³A)∩k[p,t]=(p³,pt,t²).

Indeed a monomial p^i t^j maps to p^(i+2j)Y^j, distinct monomials remain distinct, and membership is i+2j>=3. In particular t² is missing from (p³,pt). This model illustrates the incorrect general formula; it is NOT an example satisfying every invariant hypothesis of either primary theorem.

## Context and limits of the diagnosis

I reread the retained Ghosh–Gupta arXiv2206.15210v5 text lines1158–1255 (Theorem4.1 and its exponent-comparison proof), and Ghosh–Pal arXiv2404.13803v1 lines236–342 (Theorem3.2 and its proof, plus the following context). Their hypotheses identify DK and/or ML with specified polynomial subalgebras, and they assume an isomorphism between two presentations. The displayed comparison is made after assuming unequal exponents for contradiction. No restriction to expressions linear in Y, quotient killing higher F-powers, or alternative meaning of ideal contraction appears in these passages.

The DK/ML conditions explain why the coefficient rings and prime factors are preserved. They do not alter the elementary identity F^k=p^(rk)Y^k. Thus they do not, by themselves, justify (*) as an algebraic contraction computation. The impossible unequal-exponent case may ultimately be excluded by a different argument: pointing out this step does not refute the theorem's conclusion, supply a counterexample under all its hypotheses, or show that no repair exists. No whole-paper correctness audit is attempted.

## Effect on credit and T047N

The operation-level antecedent remains real and must be credited: these papers use intrinsic DK/ML subalgebras and contracted ideals to seek recovery of modification exponents, with stated isomorphism-class conclusions. The clarification limits what we can certify about the particular displayed higher-contraction calculation; it does not erase that prior strategy or establish novelty for our work. No claim that T047N is substantial follows from a problem in an antecedent's displayed step.

Frozen T047N §7 does not invoke (*). It independently proves the complete reduced contraction staircase

    ((p^r A_n)∩S_n + pS_n)/pS_n = I^ceil(r/n).

Its upper inclusion uses the exact cancellation-controlled associated graded ring; its lower inclusion retains all products of the generators lifting I. The already frozen diagnostic's truncated-two-generator control expressly detects omitted higher powers. The correctness and contribution level of T047N remain questions for the independent gates.

Original prose: Myeongjin Kang, no affiliation, CC BY4.0. Parent independently noticed the same displayed issue and requested this clarification. No source bodies are copied here, and the frozen r29 inventory remains unchanged.
