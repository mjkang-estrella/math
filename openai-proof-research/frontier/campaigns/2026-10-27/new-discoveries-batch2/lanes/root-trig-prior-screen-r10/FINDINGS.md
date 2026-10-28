# Primary-source exclusion: generalized Cusa–Huygens conjecture

Date 2026-10-28. Credit 0; no discovery nominated, no Lean investment.

The 2019 survey by Yin–Huang–Wang–Lin, JMI 13(3), Open Problem 7.1 on
printed p.851, repeats Klén–Vuorinen–Zhang Conjecture 3.29:

    sinh_p(x)/x < (p+1)/(p+cos_p(x)), p>2, 0<x<pi_p/2.

Root read the exact original statement in arXiv:1210.6749v1, Eq.(3.30),
and the survey's actual PDF text. This is stronger than the original paper's
proved bound 3/(2+cos_p(x)); that weaker theorem alone does not settle it.

**Decisive public prior result:** Bao-ju Sun, *Some inequalities for the
generalized trigonometric and hyperbolic functions*, CSET 2016, Atlantis
Press, pp.251–254. Theorem 11 on p.254 is the exact same inequality with
the same domain. Full publisher PDF obtained lawfully at
<https://www.atlantis-press.com/article/25859267.pdf>, saved as
sources/sun2016.pdf with SHA-256 in sources/retrieval.json. Root visually
read the actual theorem and full proof on the last page, retained as
sources/sun2016-page4.png; text extraction is also included.

The proof uses f(x)=(p+1)x-p*sinh_p(x)-sinh_p(x)*cos_p(x). With
s=sin_p(x), c=cos_p(x), y=sinh_p(x), z=cosh_p(x), t=tanh_p(x), it obtains

    f'' >= y*t^(p-2) * H(c),
    H(u)=2*u^(2-p)-p+(p-1)*u^(3-p)-u > 0  (0<u<1,p>2).

The comparison uses s>t and z*s>y, together with p-2>0. Sun's Lemma 6
establishes H>0: for p>=3, H'<0 directly; for 2<p<3,
H''=(p-1)(p-2)u^(-p)[2-(3-p)u]>0, and H'(1)=-p(p-2)<0.
Thus H'<0 on (0,1) and H(1)=0. Two integrations from f(0)=f'(0)=0
give the claimed strict inequality. This records the actual proof mechanism,
not merely an abstract or title match. No upstream Lean replay is claimed.

The 2019 survey's open label does not override this published 2016 theorem.
Do not count a rediscovery, a re-formalization, or a parameter instance.
This exclusion does not settle its separate sine parameter-concavity
threshold question (Open Problem 7.2).

## Separate lead, not a finding

Svinin arXiv:1610.05387v2 was read through Sections 2–7 as a possible
new direction: Conjecture 5.2 is MathDB 334352's coefficient-shape question.
The public trureturing Svinin record inspected here instead treats the
different 2015 difference-equation identity, arXiv:1505.06394v2; it cannot
be used to mark this 2016 sum-of-powers question solved. No proof,
counterexample, novelty clearance, source-level Lean or acceptance for
334352 has been produced here. Continue only after wider same-object prior-art
and source reconstruction. ArXiv v2 (2017-03-01) is latest in its live history;
its HTML's dynamic 2026 date must not be mistaken for a new revision.
