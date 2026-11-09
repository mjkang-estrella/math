import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).parent; C=P.parent; B=C.parent
literal=json.loads((P/'literal-index.json').read_text())
reasons={
337558:'Character bijection on p-prime degrees requires all partitions and normalizer representations. Literal final universal Irr quantifier exceeds displayed domain; do not credit that domain correction. Next: restore source bijection quantifier and hook-degree divisibility mechanism.',
337569:'Generic equal-degree minimal resolutions: no finite exact genericity certificate or full syzygy construction identified. Next: source characteristic/genericity assumptions and an explicit universally generic ghost-term mechanism.',
337604:'Literal family and invariant notation destroyed despite full tag. Next: restore inverse-Turan multigraph invariant and cycle multiplicity convention from actual primary body. No interpretation credited.',
337625:'Three-route investigation; endpoint perturbation fails for a known non-open-convex code, not the reserved open-convex target. Missing global endpoint-order lemma and literal minimum-dimension Lean bridge. See proof-notes.md.',
337633:'Displayed syzygy bidegrees and p expression need primary restoration; do not exploit malformed indexing or low-degree endpoints. Full Schur-module identification and semantic library absent.',
337684:'Sufficiently-large-diameter classification, not a single exceptional graph. No arbitrarily-large-diameter nonlisted family or full classification mechanism found.',
337690:'Full flag-sphere gamma2 lower bound; corpus refuted snippet concerns stronger real-rootedness, not this statement. No full topological inequality proof supplied.',
337698:'Missing definition m(G), base-field restrictions and threshold dependence. A single extension cannot refute sufficiently-large group assertion. No source-fidelity proof.',
337733:'Suspected extraction error: characterizing monoids rather than class groups. Adjoining units preserves sets of lengths and changes monoids routinely; that is a wording correction, not new credit. Primary body unread, intended group characterization not resolved.',
337776:'Mixed-VMHS functional transcendence requires period-map definitions and weakly-special closures. No primary proof-body review or claimed novelty clearance; next compare actual later mixed Ax-Schanuel theorems.',
337828:'Volume infimum over lift complements requires hyperbolic lift class and volume comparison. No certified full-scope topological construction.',
337846:'Local maximum does not imply global Finsler isoperimetry. Exact F_B metric and Holmes-Thompson area needed; no global comparison or certified rival curve.',
337879:'Elementary private-triangle attachment to C5 refutes general criterion. Actual original conjecture read. Routine finite construction excluded from substantive discovery credit; no Lean investment.',
337909:'Exact local/global automorphic factorization and normalization, no finite surrogate can supply period identity. Restore all local factors before investment; no ordinary or formal endpoint.',
337930:'All proper colorings and colored tree copies essential; finite uncolored search would not settle the extremal inequality. No all-tree embedding mechanism.',
337971:'Phi and gamma range unspecified in literal. Need source stabilization-polynomial definition and nondegenerate admissible gamma; do not count gamma0 or a routine domain repair.',
337987:'delta2 and delta3 omitted. Cannot test integer formulas without restoring parity cases. No coset-leader certificate or full-scope ordering proof.',
337995:'Asymptotic power saving with arbitrary k<l; finite counterexample cannot refute an O bound. Missing cycle-family definition and uniform counting argument.',
338002:'All solid partitions and coherent sign choices; finite q verification not proof of formal series equality. No full combinatorial or orientation mechanism.',
338010:'Strongest parked finite-object target. Exact join subclass enumeration reaches40/11; arbitrary graph discharging lemma missing. Actual source theorem/proof bodies read. See proof-notes.md.',
338016:'Scaling constraints may couple p and h; primary asymptotic tiling free-energy function not restored. No optimizer proof or certified asymptotic unequal-slit improvement.',
338084:'Sharp all-group subset-sum bound and attainability; empty-set exception is an endpoint correction, ineligible. No substantive new construction or full sharp proof.',
338146:'General broom degree-power extremality for sufficiently large n; B and H definitions omitted. Small n cannot refute eventual assertion. Need parameter-dependent family or full stability proof.',
338147:'Literal mathematical ranges and theorem number destroyed. Primary restoration required before any exact conjecture can be stated. Not reviewed as a complete mathematical target.',
338224:'Infinite square-free ternary words and pointwise factor-complexity comparison. No certified alternative infinite word or complete factor-language analysis.',
338225:'G definition missing, and critical exponent requires all finite factors. No morphic-word proof or certified full complexity bound.',
338227:'All s-saturated families. Small s known cases or one finite bound do not solve general sharp inequality. No full partition/measure argument found; source body not read.',
338262:'Projective planes of prime order; low-prime weight coincidences are endpoint artifacts and ineligible. Full weight-count rigidity would require incidence/code semantic library.',
338308:'All finite graphs; regular versus locally irregular decomposition meanings must be kept distinct. No three-part constructive induction or obstruction found.',
338311:'Centered distributional maximum limit; finite samples cannot establish convergence. No terminal-process coupling or extremal limit theorem read.',
338329:'Need actual source distinction between existence of straight diagrams and crossing-minimal OGC codes before treating rational-knot inclusion as new. No source-body review or proof claimed.',
338405:'Universal logarithmic bipartite induced minimum-degree bound; random cut gives bipartite subgraph, not induced bipartite subgraph. Missing independent-parts construction and degree retention.',
338406:'Existential d0,g0 constants cannot be refuted by a bounded small graph. Need unbounded-girth/high-degree obstruction family or full constructive theorem.',
338407:'Maximum-degree1 log endpoint gives only routine domain correction, excluded. Intended asymptotic separation-choosability bound requires all separated list assignments; no full coloring mechanism.',
338423:'Corpus Santos snippet alone does not refute a source-to-sink directed path statement; ordinary Hirsch and strict monotone Hirsch are distinct. Primary counterexample body not read; no resolution claimed.',
338430:'Actual Simpson Conj0.5 read, still conjectural in that body. Misattached1995 solved note concerns ordinary square avoidance. Circular successor does not solve linear bound. No new lower-bound proof.',
338431:'Public exact overlapping refutation: Bhattacharjee Hexagon2610.00473v2 Cor1.2 explicitly gives cyclic ababab and alternating family, with full Sections2-4 proof read. Exclude rediscovery; no Lean replay of public work claimed.',
338434:'Full linear Golomb-Welch/abelian Cayley bound. Lee-ball cardinality alone is counting, not strict nonexistence. No group-ring contradiction for all d>=3,k>=2.',
338441:'Primary source explicitly refutes classification after replacing C2 by C2-prime. That does not itself refute original weaker C2 literal; keep logical distinction. Full original-conditions counterexample not supplied. No corrected-condition variant credit.',
338464:'Informal stability claim lacks exact variation class, regularity, order bound and quantifiers. Smooth flat-function shortcut not justified for this length functional; no full-scope proof.'}
sources={337625:['1711.03185','convex-prior'],337879:['1712.02324'],338010:['1712.07769'],338430:['1802.04481'],338431:['1802.04481','circular-prior'],338441:['1802.04921']}
out={}
for k,v in literal.items():
 i=int(k);rec=v['record'];raw=(P/'literal'/f'{i}.jsonl').read_bytes()
 assert raw.endswith(b'\n') and hashlib.sha256(raw).hexdigest()==v['raw_sha256']
 out[k]={'mathdb_id':i,'title':rec['title'],'literal_statement':rec['statement'],'literal_inspection':True,'raw_line_path':f'literal/{i}.jsonl','raw_line_sha256':v['raw_sha256'],'newline_preserved':True,'corpus_chunk':v['chunk'],'full_chunk_sha256':v['chunk_sha256'],'line_number':v['line_number'],'primary_passages_read':sources.get(i,[]),'proof_body_review':{337625:'Original endpoint procedure and later indexed Theorem4.3 argument; not a target proof',337879:'Surrounding source perfection argument',338010:'Lem6.1, Thm6.3 and Thm6.5 proofs',338430:'No proof of Conj0.5 exists in original passage',338431:'Successor Sections2-4 through proof of Thm1.1; independent witness checked, no kernel replay',338441:'Introduction conditions and corrected-condition example only; no full target proof review'}.get(i,'none'),'status':('excluded_public_overlap' if i==338431 else 'excluded_routine' if i==337879 else 'parked_after_mechanism_attempt' if i in [337625,338010] else 'screened_literal_only' if i not in sources else 'screened_primary_passage'),'reason_and_next_lemma':reasons[i],'ordinary_full_scope_proof_complete':False,'lean_endpoint_complete':False,'credit':0,'global_unreviewed_status_claimed':False}
assert len(out)==40 and set(map(int,out))==set(json.loads((P/'reservation.json').read_text())['ids'])
(P/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
paths=[C/'AGENTS.md',B/'AGENTS.md',B.parents[2]/'AGENTS.md',C/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json',P/'reservation.json',C/'intricacy-parent-final-r1/registry-head-receipt.json']
receipts=[]
for f in paths:
 if f.exists():receipts.append({'path':str(f.resolve()),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
(P/'context-receipts.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_references':receipts,'accepted_campaign_ids_excluded':[388087,333569],'other_explicit_protections':[324342,330264,335230,326640,332204,337160],'historical39':'All accepted families in inherited ledger/prior-campaign-context excluded; none nominated','human_note_search':'Bounded all40-ID Markdown search excluding sources/frozen/extracted in prior-human-hits.log. Empty output is not global unreviewed clearance. Prior ledger rejection reasons inspected; no old rejected endpoint selected.','historical_access_failures':'Inherited MathDB and Palomar403 retained by reference, not retried. New direct convex publisher404 recorded once.'},indent=2))
(P/'search-receipts.json').write_text(json.dumps({'date':'2026-11-01','method':'public web search and indexed primary fulltext; no browser tabs','queries':['1712.07769 triangle conjecture','1802.04481 circular abelian squares conjecture','1711.03185 conjecture dimension','Franke Muthiah conjecture codes dimension','BT(3) triangles conjecture Kirsch','circular abelian squares minimum conjecture Simpson proof'],'primary_followups':['https://hexagonmath.org/2610.00473v2','https://hexagonmath.org/pdf/2610.00473v2','https://malayajournal.org/articles/MJM0S201153.pdf'],'chronology':'Hexagon page header says22Oct, version-history27Oct; PDF itself dated27Oct2026. Both precede this lane. No earliest-priority assertion.','limitations':'Search misses do not clear novelty. Primary bodies read only as individually recorded. No global registries/body survey claimed.'},indent=2))
print('VALIDATED: 40 exact IDs, 40 newline-preserving raw lines, ID-keyed results; zero credit.')
