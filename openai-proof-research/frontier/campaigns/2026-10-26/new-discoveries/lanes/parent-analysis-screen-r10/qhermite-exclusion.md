# MathDB336243 excluded: source successor already proves it

Actual arXiv1706.00316v9 (26May2021), Theorem3 equation(5.10), p.18, supplies
the exact all-n expansion requested by the older source conjecture. Its proof
in Section6, pp.23–25, was read: the reciprocal expansion follows from
Poisson–Mehler and the q-binomial theorem; substituting q->1/q and converting
h_n to b_n gives equation(5.10).

Writing (q)_r=prod_(k=1..r)(1-q^k), the source formula gives

    beta_(n,j)(q)=(-1)^j*q^[binom(n,2)-binom(n-2j,2)-j+binom(j,2)]
                  *(q)_n/((q)_j*(q)_(n-2j)),

and beta_(n,0)=1. This is precisely the older requested form after factoring
(-1)^n*q^[-binom(n,2)]. The limiting q=0 reading is explicitly discussed by
the author; no new endpoint correction is claimed.

Source: https://arxiv.org/abs/1706.00316v9 . The separate multivariate common
denominator Conjecture1 remains a different question and is NOT excluded here.
No Lean/paper/discovery credit for this rediscovery.
