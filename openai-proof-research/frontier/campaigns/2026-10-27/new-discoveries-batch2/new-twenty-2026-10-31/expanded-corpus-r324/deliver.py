import re,datetime
V=json.loads((P/'provenance.json').read_text())
notes={
'367266':('park_topological_gap','Arbitrary circle graphs require a global homotopy decomposition. Wedges constructed in one direction do not establish the converse; no contractible-link recurrence or torsion witness proved.'),
'367305':('hold_definition_complexity_gap','Block construction is source-dependent. A polynomial reduction must simulate local cover constraints and preserve simple inputs in both directions; no such full gadget proof supplied.'),
'367308':('hold_public_resolution_body_unread','Latest source Conjecture 7.3 footnote announces Bonin proof. Actual Bonin body unread; conflicting cached refuted tag cannot establish either resolution. No credit and no retry plan.'),
'367336':('exclude_domain_diagnostic_only','Edgeless n=2,m=0 diagnostic violates nonempty complete-bipartition conclusion; empty parts make it vacuous. Domain correction only; intended dense problem unresolved here.'),
'367339':('park_analytic_gap','Need strict nonvanishing of the rank-four exterior-square invariant along every generic extremal at every positive time. Cut-time bounds and isolated numerical times cannot supply global avoidance.'),
'367387':('hold_basis_positivity_gap','Classification of single SEMs does not rule out a positive sum of several SEMs. Need full coefficient-sign theorem with the primary basis definition; no finite computation was run.'),
'367511':('hold_partition_extension_gap','Three ordinary routes sustained in ATTEMPTS.md. Common antineighborhood of each edge is H-free; no D_(k-1) maximum-clique transversal follows. Exact general claim remains unproved.'),
'367522':('park_complexity_reduction_gap','Variable-round hardness is explicitly distinguished from repeated rounds in the record. A reduction must preserve the same pile count and exact repeated operation; no complete encoding supplied.'),
'367540':('hold_definition_and_CM_gap','Cutset accessibility alone in record may omit unmixedness from intended accessible-graph definition. No correction counted. Intended Cohen–Macaulay characterization requires commutative-algebra proof beyond this lane.'),
'367546':('hold_uniform_saturation_gap','Source-family completed r306 hold retained. Boundedness is uniform in n, not a finite-family check. Adding a top may introduce induced copies and does not prove both uniform implications.'),
'367668':('park_analytic_genericity_gap','Genericity and boundary-condition class need precise primary interpretation. Exceptional resonant lengths cannot refute a generic assertion. No observability proof supplied.'),
'367681':('exclude_identification_correction_and_classical_bridge','Full lattice-count argument and exact 7-versus-9 identification diagnostic in ATTEMPTS.md. Literal Pan equality is a parameter/identification correction; repaired Schubert formula follows complete older split-block count plus coordinate symmetry. Zero discovery credit.'),
'367709':('hold_literal_dimension_correction_only','Rectangular transpose cannot be equivalent by row/column permutations when n differs from m. Literal tautology is not the intended plethysm inequality. No correction or known Foulkes subcase counted.'),
'367921':('hold_instability_type_gap','Need primary Type I/II definitions and a nontrivial-instability proof. Arbitrary product symmetries do not certify failure of Type I. No exact graph/automorphism witness supplied.'),
'368034':('hold_classical_resolution_scope','Primary introduction reports Kim–Roush counterexamples to unrestricted Williams conjecture; source new theorem has GK-dimension-three restriction. No prior counterexample re-credited; counterexample proof body not read.'),
'368069':('hold_uniform_interval_bijection_gap','Source Conjecture 5.2 located. Equality of element counts or m=1 equivalence does not count intervals for all parameters. Need endpoint-preserving interval bijection or exact general formula.'),
'368124':('park_global_Hamiltonicity_gap','Primary Conjecture 1 and rose-window Theorem 1.1 context read. Containing a connected Hamiltonian spanning rose-window/Haar subgraph handles only subfamilies; no proof every bicirculant contains one.'),
'368218':('hold_character_cancellation_gap','Primary Conjecture 5.1 and Theorem 5.2 context read. Alternating f-vector sum may cancel; complete plucking sufficient cases do not exhaust Rev(P). No nonzero invariant or valid counterexample supplied.'),
'368257':('hold_spark_lower_bound_gap','Primary Conjecture 4.2 located. Constructing a dependence gives only a spark upper bound. Need universal independence of all smaller subsets plus BIBD incidence counts, neither proved.'),
'368306':('hold_general_game_strategy_gap','Triangle-free and fixed-edge-free-involution subcases proved in ATTEMPTS.md. General transitivity does not give either. Isolated-vertex K2 variant is an excluded domain correction, not a candidate.')}
receipts=[json.loads(l) for l in (P/'http-receipts.jsonl').read_text().splitlines()]
primary_depth={
'367681':'Definitions, target conjecture across v1/v2/v3 (selected passages), independent convex-hull/counting bridge; companion introduction and Section 3 actual coefficient-extraction proof body. Not full Section 4 proof audit.',
'367511':'Entire short v1 primary ordinary body including Definition 2.1 and all theorem proofs; later-version/journal/citing-body coverage incomplete.',
'368306':'v1/v2 rules and Conjecture 6, actual local Proposition 5 proof body, clique consequence. Later biased game results not a full audit.',
'367336':'v1 Conjecture 3 and Example 33/captions as text; no visual figure inspection.',
'367308':'Latest HTML Conjecture 7.3 and Bonin announcement footnote; no announced proof body.',
'368034':'Latest HTML introduction and classical-counterexample/GK-three scope discussion; no Kim–Roush proof body.',
'368069':'Latest HTML Conjecture 5.2 and reference context only.',
'368124':'Latest HTML Conjecture 1, Theorem 1.1 and subsequent spanning-subgraph discussion only.',
'368218':'Latest HTML Conjecture 5.1 and alternating-f-vector discussion only.',
'368257':'Latest HTML Conjecture 4.2 and neighboring context only.'}
results={}
for k,v in V.items():
 record=v['parsed'];canonical=json.dumps(record,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()
 v['parsed_canonical_utf8_sha256']=hashlib.sha256(canonical).hexdigest();v['parsed_hash_encoding']='JSON ensure_ascii=False sort_keys=True separators comma/colon, UTF-8'
 related=[r for r in receipts if record['source_url'].split('/')[-1] in r['url']]
 results[k]=dict(mathdb_id=int(k),title=record['title'],literal_statement=record['statement'],full_parsed_record=record,provenance={x:y for x,y in v.items() if x!='parsed'},raw_file='literal/'+k+'.raw.jsonl',outcome=notes[k][0],finding_and_precise_gap=notes[k][1],review_depth=dict(literal='entire record and statement read',primary=primary_depth.get(k,'Retrieved source; no complete target-definition/proof review claimed. Any source output excerpt screening was incidental and incomplete.'),versions_journal_corrections_figures_citing_bodies_cleared=False),source_http=related,attempts='ATTEMPTS.md' if k in ['367681','367511','368306','367336','367709','368034','367308'] else [],historical_reconciliation='history-read-inventory.json and history-hits.json; bounded exact completed allowlist screen, numeric hits can be incidental',registry='registry-screen.json; routing only, incomplete and not novelty clearance',accepted_credit=0,source_novelty_significance_holds='retain all; none cleared',dormant_actual_semantic_pi_plan=None,formal_endpoint_complete=False)
assert set(results)==set(str(x) for x in json.loads((P/'reservation.json').read_text())['ids']) and len(results)==20
(P/'provenance.json').write_text(json.dumps(V,ensure_ascii=False,indent=2)+'\n')
(P/'results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
registry={}; read_inventory=[]
for r in receipts:
 d=dict(r)
 if 'file' in r:
  if 'github' in r['url']:
   t=(P/r['file']).read_text();heads=sorted(set(re.findall(r'"currentOid":"([0-9a-f]{40})"',t)))
   registry[r['url']]=dict(heads=heads,sha256=r['sha256'],status=r['status'],utc=r['utc'],depth='landing/candidate listing/import routing only; no proof clearance')
  if 'arxiv' in r['url']:
   matched=[k for k in results if results[k]['full_parsed_record']['source_url'].split('/')[-1] in r['url']]
   d['actual_read_depth']=[primary_depth.get(k,'retrieved, not full definition/proof read') for k in matched] or ['companion 2303.04113 selected introduction and Section 3 proof body' if '2303.04113' in r['url'] else 'metadata']
 read_inventory.append(d)
registry['limits']='Current OpenAI and LeanPool landing pages, candidate listing and import index retrieved; projects.yml guessed community paths returned 404 and do not clear the real registry. No API retries. No exhaustive tree/proof audit or current-open certification. Historical r322 metadata remains explicitly dated.'
registry['historical_snapshot']='OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb dated 2026-10-08 from completed r322 metadata; no new snapshot-body read or clearance.'
(P/'registry-screen.json').write_text(json.dumps(registry,indent=2)+'\n')
(P/'source-read-inventory.json').write_text(json.dumps(read_inventory,indent=2)+'\n')
h=hashlib.sha256((P/'reservation.json').read_bytes()).hexdigest();e=(P/'reservation.sha256').read_text().split()[0];assert h==e
(P/'reservation-after.json').write_text(json.dumps(dict(actual=h,expected=e,match=True,count=20,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
print('Exactly 20 results; reservation before/after',h,'all zero credit')
