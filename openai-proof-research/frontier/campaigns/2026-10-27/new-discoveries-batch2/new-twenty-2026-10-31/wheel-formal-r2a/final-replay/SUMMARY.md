# MathDB 371637: r2a lower bound

Both assigned endpoints are proved uniformly for every natural t >= 1 in formal/LowerWeighted.lean:

- WheelFormal.vertexWeight_independent_bound: every independent set in the actual wheelSquare t has vertexWeight sum at most 2(2t²+t+1).
- WheelFormal.wheelSquare_fractional_lower: (6t²+7t+3)/(2t²+t+1) <= fracChromatic (wheelSquare t).

There are no residual combinatorial hypotheses. No parameter enumeration is used. The two inherited r1 modules remain byte-identical. Five added proof modules establish cyclic independence, an explicit near-perfect cyclic pairing, deletion and product matchings, and all wheel bookkeeping and case bounds. The key simplification is to anchor the cyclic matching at any deleted vertex; each other deleted vertex breaks at most one pair, giving at most |A|-1 unmatched vertices without a path-component decomposition. PROOF.md explains the argument; STATEMENT-CORRESPONDENCE.md maps it to Lean.

The proof environment contains 160 audited local declarations including generated declarations, of which 79 are inherited; there are 37 named theorems, 24 new. Fresh strict replay, leanchecker for all seven proof modules, full module-by-module audits with opaque bodies, and negative controls are run by replay.py. The initial combined printing audit hit its 120-second CPU cap; its log and receipt are preserved in fresh-replay. Final verification evidence is in final-replay/logs and logs/final-replay-driver.log. No safety flags or transitive axioms outside propext, Classical.choice and Quot.sound are allowed.

The source-only packet is wheel-lower-source.zip. Inputs were copied with hash identity and checked again afterward. All writes stayed inside this lane; no git, child agents, shared-ledger edits, network access, upper-bound work or Upper*.lean modules were used. No background jobs remain at handback.

This completes r2a's lower-bound scope, not the full equality. Upper construction and coverage remain assigned to the sibling lane. Root acceptance and independent review are pending; credit remains zero. Inherited prior-art limits still apply.
