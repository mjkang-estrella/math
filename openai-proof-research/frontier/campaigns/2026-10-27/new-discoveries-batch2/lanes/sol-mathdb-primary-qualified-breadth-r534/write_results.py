from pathlib import Path
import json,hashlib
D=Path(__file__).parent;L=D.parent;B=L.parent
reasons=[
'Uniform K for all r and density deficits requires removing log r from cycle partitions; fixed r or fixed deficit does not establish the quantified bound. No short full-scope construction or obstruction.',
'Overlapping monochromatic tree covers are easier than cycle partitions but the uniform r/deficit estimate still needs a new covering mechanism. No such mechanism identified.',
'A counterexample would require an exact planar configuration with fewer than sixteen points and exactly three nearest neighbours at every point; regular abstract cubic graphs alone do not certify Euclidean distances. No coordinates or lower-bound proof.',
'Every height up to M(p), for every odd prime p, must recur for unbounded pairs of primes. Computing finitely many cyclotomic polynomials cannot certify this recurrence; no residue-class mechanism supplied.',
'Polynomial pivot-minor Ramsey bound for arbitrary graphs requires uniform control in k. Fixed excluded classes do not cover all graphs; no full route.',
'Constant-factor comparison at the same n for every infection rule is stronger than a comparison after scaling n. Padding alone does not remove that distinction without regular growth control.',
'Existence of a logarithmic growth exponent for every rule cannot follow from monotonicity and a polynomial envelope alone; no interpolation or submultiplicative law established.',
'Universal little-o separation over bipartite H needs a structural upper bound sharper than the Turan scale. Degenerate-rule/domain cases need source definitions and would not earn discovery credit.',
'Charging steps to H-minus-edge-free graphs is not justified just by the terminal closure; the minimum over edges requires a valid uniform charging argument. No bridge found.',
'All complex dimensions require an operator-norm lower bound, whereas Fourier/unimodular constructions supply only the upper bound. A low-dimensional calculation cannot settle the universal statement.',
'Primary Conjecture 1.1 and Theorem 4.1 proof read. Transpose invariance gives paired minimizers, not that each is symmetric. Two-row exchange decreases bc to c^2 but does not supply a shape-preserving all-row exchange. Conditional Theorem 1.2 cannot be used unconditionally.',
'Primary Conjecture 5.4 and definitions read; cited predecessor Corollary 5.3 and proof inspected. Its cumulative max<=n/N0 near-unimodality statement is not an all-cutoff/all-numerical-monoid theorem. Exact closed-prefix enumeration for l=2..12 found no violation. No all-l injection or finite counterexample survived.',
'Least-atom testing supplies a necessary Bernoulli upper bound, but equality needs the opposite norm inequality for every function and all 1<p<q. No valid two-level reduction established.',
'Excluding visibility in every abelian threefold is not a finite verification of the named surface alone. Needs arithmetic classification/obstruction and heavy dependencies, no small certificate route.',
'With high probability for every allowed lambda regime requires eliminating all cospectral mates of the giant 2-core. Local switching constructions require asymptotically nonvanishing occurrence; none established.',
'All degree bounds r must achieve the limiting common-cut proportion, not just the proved r=3 case. No simultaneous cut selection argument attaining (r-1)/r^3.',
'Proper colouring and a Dirac degree condition must support every allowed bounded-degree spanning tree with cn-o(n) colours. Greedy embedding alone does not control colour reuse and completion.',
'All nontrivial symmetric-group irreducibles and all weighted hypergraphs require a uniform spectral comparison. Transposition support does not subsume arbitrary hyperedge operators.',
'Arbitrary weighted hypergraphs and all U(n) irreducibles require spectral ordering, not only the two displayed candidate modules. No uniform representation comparison.',
'Both parity chains run over unbounded levels k and every nonnegative weighting. Small matrices may refute but cannot prove monotonicity; no certified reversing weight or all-level intertwiners.',
'Universal tournament-dependent exponent for simple digraphs includes the tournament Erdos-Hajnal difficulty. No bounded certificate or constructive polynomial acyclic-set mechanism.',
'Excluding all triangulations with at most 23 vertices requires a topological lower bound or certified exhaustive classification. A 24-vertex construction alone is insufficient.',
'Primary Conjecture 1.3, dual separators, Proposition 1.2 proof and Theorem 1.4 proof read. k=2 contraction deals with two separator patterns; higher k does not inherit that contraction. Small-n exceptions do not refute the sufficiently-large-n quantifier.',
'Uniform approximate sampling for all allowable colour class vectors needs mixing or another distributional algorithm, not just existence of a proper colouring. No tractable full sampling proof.',
'All phases and all real sigma require a global minimizer theorem over all continued fractions, not only crossing values at fixed points. No global comparison inequality.',
'Exact variation norm on every path length would imply infinite-lattice/real-line bounds. Testing n<=10 or step functions gives lower bounds only; no upper bound for arbitrary f.',
'Cross-ratio equality on an infinite grid must yield a globally biholomorphic surface; matching cell invariants alone needs compatibility and control of global gluing. Source class definitions unreviewed.',
'Primary Section 5 p-toppling definition and Conjecture 5.2 read. At p=0 no particle is sent, so stationarity/termination needs a domain qualification. Degree-one trivial graphs can erase strictness. Such corrections yield no substantive credit; no interior nondegenerate stochastic-order route.',
'All digraphs and all k require a simultaneous stable-set/path-partition inequality beyond Gallai-Milgram. No extension of the k=1 mechanism to all k.',
'Polynomial isomorphism-type anticoncentration for arbitrary high-minimum-degree graphs is not implied by labelled-tree counts; many labelled trees may have the same type. No orbit-uniform bound.',
'Sharp (d-1)/2 exponent for every tree type requires substantially stronger concentration control than the polynomial target. Complete-bipartite examples test sharpness rather than prove the upper bound.',
'Exact leading quadratic constant for all odd cycles of length >=7 needs a structural rainbow lower bound in every graph just above Turan density. No uniform mechanism.',
'Entire unitary dual of a general reductive group, conditional on Arthur for all Levis, needs deep classification and induction arguments. Not a short full-scope route.',
'A five-colouring of every subdivided subcubic graph must respect distance constraints across all branches. Local alternating colours do not ensure packing for higher colours; no full constructive scheme.',
'Literal all-n lower bound needs dismantling definitions. Tiny n may expose endpoint wording but earns no credit. No projection counting invariant proving the intended range.',
'Asymptotic codegree threshold 3/4 needs a spanning absorption/connecting argument beyond the reported 7/9 estimate. No bounded exact counterexample above 3/4 or shorter full proof.',
'An exact upper bound 680 requires ruling out all 681-edge C4-free cube subgraphs; maximality of the displayed construction is only local saturation. No small global inequality or infeasibility certificate.',
'Likewise exact 304 upper bound requires excluding every 305-edge Q7 subgraph. Failed randomized search is not UNSAT; no bounded proof certificate obtained.',
'All k>=4 threshold positions require both boundary conjectures for iterated multiplicities. Observing Golomb recurrence finitely far does not prove closure at every return.',
'Every regular parameter vector needs source-specific spectral gap and multiplicity definitions. Numerical eigenvalue coincidence is not algebraic multiplicity certification; no exact degeneracy mechanism.',
'Every rational exponent needs a single induced-forbidden bipartite graph valid for every s>=s0. Existing displayed a/b range does not cover all r; no new graph family.',
'Every rational in [1,2] for a single forbidden graph is stronger than rational-exponent constructions for forbidden families. Endpoint/classical instances receive no credit.',
'Uniform exact affine saturation formula requires the meaning of c and intended n range from primary source. n<k/domain corrections would not resolve substantive asymptotic content.',
'All m>=2n-1 in both parities require the sharp star-wheel upper bound; checked parameter values cannot extend the full range. No common extremal reduction.',
'Equivalent minimum-degree wheel formulation requires sharp parity-sensitive wheel embedding for all 3<=k<n/3. A basic neighbourhood cycle theorem does not automatically attain the threshold.',
'R_vm(5)=15 requires all 15-vertex graphs plus a 14-vertex obstruction, with local-complementation equivalence controlled. Raw graph enumeration is too large without a classified reduction; no small certificate.',
'All acyclic F requires a subdivision-forcing outdegree bound despite unrestricted indegrees. A greedy directed-path argument lacks a robust escape condition; no universal embedding route.',
'Worst generating-set diameter in every transitive group cannot be inferred from diameter of one convenient generating set. No uniform word-length mechanism; conditional Babai reduction is insufficient.',
'Existence of one degree threshold for every 2-connected odd-order graph needs global odd-edge-colouring construction. High degree alone does not supply parity-compatible decomposition.',
'All n,k with a uniform additive constant requires precise switch and degree-threshold definitions; divisibility lower bounds and k=2,3 upper bounds do not give general k. Not a short extension.'
]
rows=json.loads((D/'assigned-records.json').read_text());assert len(reasons)==len(rows)==50
primary={373166:('2602.14931v1',[[803,920]]),373188:('2602.15754v1',[[411,430],[641,689],[1935,2002]]),373497:('2603.08123v1',[[245,300],[320,500]]),373656:('2603.16304v1',[[1650,1740]])}
res=[]
for x,reason in zip(rows,reasons):
 a=x['record'];i=a['mathdb_id'];d={k:x[k] for k in ('corpus_chunk','line','statement_sha256','canonical_record_sha256')};d.update(mathdb_id=i,title=a['title'],statement=a['statement'],source_url=a['source_url'],canonical_url=a['canonical_url'],disposition='HOLD_NO_FULL_SCOPE_ROUTE',technical_reason=reason,statement_review='literal full statement including quantifiers read',primary_passage_read=i in primary,whole_body_read=False,local_proof_read=i in [373166,373497],full_dependency_audit=False,current_registry='HOLD unavailable; zero MathDB requests',successor_body_clearance=False,novelty_cleared=False,accepted_credit=0)
 if i in primary:
  v,ranges=primary[i];d['primary_evidence']={'version':v,'url':'https://arxiv.org/html/'+v,'derivative':v+'.txt','line_ranges':ranges}
 if i==373188:d['prior_body_evidence']={'version':'2412.05857v1','url':'https://arxiv.org/html/2412.05857v1','passage':'Corollary 5.3 and proof','lines':[1565,1615],'limit':'Selected predecessor proof, not whole body or successor clearance'};d['calculation']='bounded-calculation.json: no violation l=2..12'
 res.append(d)
(D/'dispositions.json').write_text(json.dumps(res,ensure_ascii=False,indent=2)+'\n');(D/'proposals.json').write_text('[]\n')
# Bind guard and instruction files; prior context already bound before reading.
f=json.loads((D/'flat-bindings.json').read_text())
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',B/'AGENTS.md',B.parents[3]/'AGENTS.md']:
 if p.exists():
  b=p.read_bytes();f.append(dict(path=str(p.resolve()),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(D/'flat-bindings.json').write_text(json.dumps(list({x['path']:x for x in f}.values()),indent=2)+'\n')
# Compare assigned IDs with administrative exclusion records without treating a nonmatch as scientific clearance.
ctx=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;t=p.read_text();ctx.append({'file':str(p),'assigned_id_literal_matches':[x['record']['mathdb_id'] for x in rows if str(x['record']['mathdb_id']) in t],'limit':'Text-ID comparison only, not thematic or theorem-body novelty clearance'})
(D/'context-review.json').write_text(json.dumps(ctx,indent=2)+'\n')
