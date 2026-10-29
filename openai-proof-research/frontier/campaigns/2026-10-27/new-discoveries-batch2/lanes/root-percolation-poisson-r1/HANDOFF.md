# Gladkov implied Poisson parameters: research handoff

No proof or counterexample; credit zero. Source arXiv2408.08457v2, Conjecture10.2
(printed p19), MathDB364374. For independent bond percolation, let X be the
maximum number of edge-disjoint open paths between two fixed vertices. Define
lambda_k by P(X>=k)=P(Poisson(lambda_k)>=k). The full conjecture says lambda_k
is nonincreasing. Endpoint conventions are not a discovery target.

The actual v2 HTML/PDF/text and author page are in sources/. The recent
retrieval pins omega825c45ec540a33564ceff35e4e368ddc0e95f6ae and
OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; complete relevant subtree
responses are retained. No exact named match found; this is not body-wide
novelty clearance. Check current heads before significant investment.

The nearby OpenAI finite-hypergraph joint-connection comparison is saved in
upstream-comparison.tex (with introduction/exploration). It states
P(o connected to A and T) >= P(o connected to A) min_a P(a connected to T).
No bridge to maximum-flow tail Poisson parameters has been established.
Accept this pinned upstream theorem as true per repository rules.

Earlier root-new-targets-r14/percolation_probe.py covered all K6 configurations
and 601 probability vectors, with no violation. Do not merely repeat that scan.

A possible new route, UNTESTED: independent Poisson capacities on a small base
graph. Each capacity is a limit of N parallel Bernoulli(lambda/N) edges; replace
each parallel edge by a private two-edge path to obtain a simple graph. Thus a
strict finite-threshold counterexample in the Poisson-capacity limit can be
transferred to sufficiently large finite simple bond graphs. Threshold k only
needs capacities clipped at k, allowing finite min-cut enumeration. Validate
the limit and exactify any numerical trigger; floating inversion near tail
probability zero/one is unsafe. No code or successful test of this route exists
in this root lane yet. General min-cut log-concavity is not an established
black box here. BK's submultiplicative tails alone are insufficient.

Public searches for Gladkov/implied-Poisson/disjoint-occurrence/max-flow
log-concavity found no exact resolution in a bounded search. Potential primary
background: van den Berg1996 marked-Poisson BK paper (CWI2208D.pdf), not yet
body-read. Do not infer the target from its abstract. Source citation corpus,
journal comparison and general subsumption remain incomplete.
