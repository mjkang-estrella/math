# Finite substitute for the Fourier anti-concentration step

Root-derived implementation route, not a separate discovery. This changes neither the source endpoint nor the candidate's already-reviewed ordinary proof. Independent checking is requested before formal use.

Let B_i be independent Bernoulli(p_i), i=1,...,m, with a<=p_i<=1/2 and a>0. Introduce mutually independent U_i~Bernoulli(2p_i) and V_i~Bernoulli(1/2), and put B'_i=U_i V_i. The B'_i have exactly the original independent Bernoulli law. Set K=sum U_i and mu=E K=2 sum p_i>=2am. Conditional on the complete U-vector, sum B'_i has the Binomial(K,1/2) law. Var K=sum 2p_i(1-2p_i)<=mu, so Chebyshev gives P(K<mu/2)<=4/mu.

For every integer k>=0, the largest atom of Binomial(k,1/2) is at most sqrt(2/(k+1)). An elementary proof uses unimodality and central coefficients. Put c_l=binomial(2l,l)/4^l. Then c_0=1 and c_(l+1)/c_l=(2l+1)/(2l+2). Induction yields c_l^2<=1/(l+1), because

    (2l+1)^2 (l+2) <= 4(l+1)^3,

whose right-minus-left is 3l+2. For k=2l the maximal atom is c_l; for k=2l+1 it is c_l(2l+1)/(2l+2). Both obey the stated bound. No Fourier transform, integral or limit theorem is needed.

On K>=mu/2, the maximal atom is at most 2/sqrt(mu). Thus for any real interval I of length at most w>=0,

    P(sum B_i in I) <= 4/mu + (floor(w)+2) 2/sqrt(mu).

The interval bound counts at most floor(w)+2 integers and uses the bad-event probability only once. It is uniform in the interval location, so it survives arbitrary translations and mixtures of the diamond cells.

For the Zeckendorf cells p_i>=1/(2n+1), mu>=2m/(2n+1)>=m/(2n). If m>=c^n, the bound becomes

    8n/c^n + 2(floor(w)+2) sqrt(2n/c^n).

This tends to zero for w=3n^6 and any fixed c>1. Adding the probability of cells with fewer than c^n slots gives exactly the required unconditional concentration conclusion, with different harmless constants.

The abundance estimate can also use Chebyshev after the established adaptive-binomial domination: if the dominating Binomial(J,p) has mean nu=Jp, then P(Binomial(J,p)<nu/2)<=4/nu, which tends to zero. Since nu/2>=c^n eventually, this is enough for the candidate. A Chernoff exponential bound is unnecessary there. The suffix estimate still uses the iterated no-split hazard and its elementary geometric/exponential bound.

Formal residuals remain material: finite independent-law construction, conditional mixture or direct summation identity, binomial unimodality and central-coefficient induction, Chebyshev, adaptive domination, exact legal-word partition and weights, suffix hazard, sigma-algebra endpoint and asymptotics. This note supplies an ordinary finite-probability alternative; it is not a Lean certificate or completed feasibility audit.
