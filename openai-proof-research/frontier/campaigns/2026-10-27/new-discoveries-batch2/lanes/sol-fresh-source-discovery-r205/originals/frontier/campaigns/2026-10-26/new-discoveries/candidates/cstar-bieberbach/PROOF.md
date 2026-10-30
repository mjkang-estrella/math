# Proposed entire injective C*-power-series counterexample — credit0

Target: Krishna, Preprints202208.0140v1, DOI10.20944/preprints202208.0140.v1, Conjecture1.2 and its derivative-convergent general-coefficient form1.4. Source actual PDF text read via web PDF tool at printed pp2–3, not yet visually read or downloaded as genuine local bytes. The current source page states v1 is latest. Its Dstar is literally the norm-open unit ball. It asks a_n a_n*<=n²1 and a_n* a_n<=n²1 for a normalized A-valued power series injective on that ball. Source hypotheses allow arbitrary coefficients, no requirement invertible. The invertible-coefficient1.3/1.5 assertions are distinct and NOT claimed.

Let A=C([0,1],C), tau(t)=t. Fix K>0, e.g. K=8. Put a_1=1 and a_n=(K tau)^(n−1)/n! for n>=2. Define F(u)=sum_{n>=1} a_n u^n. For every u in A, sum norms <= ||u|| sum_{n>=1}(K||u||)^(n−1)/n! < infinity. Thus it converges in A on all of A, not merely its unit ball; its derivative series also converges everywhere (bounded by an exponential). At t>0,

 F(u)(t) = [exp(K t u(t))−1]/(K t),

while F(u)(0)=u(0). These formulas follow by uniform convergence and the scalar exponential series, including the removable singularity at0.

INJECTIVITY ON ALL A: Assume F(u)=F(v). For t>0, exp(Ktu(t))=exp(Ktv(t)). Thus h(t)=Kt(u(t)−v(t)) belongs to 2pi i Z. At t=0, h(0)=0, so the same fiber condition holds there. h is continuous on connected[0,1], its values lie in a discrete set, hence h identically0. For t>0 this gives u(t)=v(t); at0 equality follows either from F(u)(0)=F(v)(0) or continuity. Therefore F is injective globally.

COEFFICIENT FAILURE: a_2(t)=K t/2. At t=1, a_2 a_2* = K²/4 >4 for K>4. For K=8 it is16>4; norm(a_2)=4>2. This violates BOTH source order bounds for n2. Arbitrarily large K gives unbounded normalized coefficient norms at every fixed n>=2, not an endpoint/transcription change. All derivative series converge, so same construction refutes1.4. The a_n vanish at0 (n>=2), so invertible-coefficient variants are not touched. Count this whole family and all same-construction corollaries at most ONE prospective outcome.

MATHEMATICAL CAUTION: injectivity here is the literal global C*-algebra function property. Scalar fibers may be noninjective; a global collision would require a nonzero integer exponential period that cannot appear continuously from the anchor t0. The usual several-complex-variable triangular shear is not an A-coefficient power series and is not cited as proving this result. No finite sampling is a proof. Norm convergence, actual scalar-exponential identification, global branch rigidity and literal source order comparison all need Lean before acceptance.

EARLY NOVELTY SCREEN: local read-only trureturing Problems+Library contains no Bieberbach delivery except a mention in the distinct higher-order Smale entry. Four targeted web searches on the exact C*-algebraic title and counterexample/refutation/exponential surfaced only the source and unrelated scalar/geometric work. This is a bounded negative search, not novelty clearance. Need full independent prior-art/source/substantive review, especially earlier holomorphic superposition operators/Nemytskii injectivity, before count. No MathDB id identified yet. No formal/paper/acceptance claim.
