from pathlib import Path
import json,hashlib,collections,datetime,re
R=Path(__file__).resolve().parents[1]; B=R.parent
rows=[json.loads(x) for x in (R/'logs/ReviewerAudit-final.log').read_text().splitlines() if x.startswith('{')]
summary={'count':len(rows),'by_module':dict(collections.Counter(x['origin'] for x in rows)),'axioms':sorted({a for x in rows for a in x['axioms']}),'all_have_values':all(x['value_present'] for x in rows),'all_safe_total':all(not x['unsafe'] and not x['partial'] for x in rows)}
assert summary['all_have_values'] and summary['all_safe_total']
(R/'receipts/audit-summary.json').write_text(json.dumps(summary,indent=2))
(R/'logs/declarations.jsonl').write_text('\n'.join(json.dumps(x) for x in rows)+'\n')
for name in ['openai-tree','omega-D5','omega-Problems']:
 d=json.loads((R/'downloads'/name).read_text()); matches=[x['path'] for x in d['tree'] if re.search(r'sigma.?t|irregular|(?:^|[/_])variance|triangle.free|365710',x['path'],re.I)]
 (R/'logs'/(name+'-screen.json')).write_text(json.dumps({'entries':len(d['tree']),'truncated':d.get('truncated'),'matches':matches},indent=2))
for p in (R/'fresh/Sigma').glob('*.lean'):assert p.read_bytes()==(B/'sigma-formal-r2/Sigma'/p.name).read_bytes()
after={str(p.relative_to(B)):hashlib.sha256(p.read_bytes()).hexdigest() for name in ['sigma-formal-r2','sigma-formal-r1','expanded-corpus-r60','sigma-source-review-r1'] for p in sorted((B/name).rglob('*')) if p.is_file()}
(R/'receipts/after.json').write_text(json.dumps(after,indent=2))
before=json.loads((R/'receipts/before.json').read_text()); changes=[p for p in set(before)|set(after) if before.get(p)!=after.get(p)]
(R/'receipts/preservation.json').write_text(json.dumps({'unchanged':not changes,'changed_paths':changes,'bound_files':len(after),'prebaseline_orientation_reads_disclosed':True},indent=2));assert not changes,changes
results=[json.loads(x) for x in (R/'logs/results.jsonl').read_text().splitlines()]
last={x['label']:x for x in results}
required=[x+'-checker-tree' for x in ['Basic','Identity','Attainment','PathExtension','Structure','DartDeficit','ConfigurationCount','Gap','Bracketing','BipartitionValue','Endpoint','NegativeControls','ReviewerSanity']]+['ReviewerAudit-final','ReviewerSanity-final']
assert all(last[x]['exit']==0 for x in required)
metrics={'max_sampled_RSS_bytes':max(x['peak_RSS_bytes'] for x in results),'max_command_wall_seconds':max(x['wall'] for x in results),'initial_harness_failure_events':[x for x in results if x['exit']!=0 and x['expected']==0]}
(R/'receipts/validation-summary.json').write_text(json.dumps(metrics,indent=2))
v={
 'review_date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'role':'Independent adversarial review; NOT acceptance; root alone accepts',
 'technical_verdict':{'gate_A':'PASS','gate_B':'HOLD','strict_extracted_rebuild':'PASS','per_module_leanchecker':'PASS','full_local_declaration_audit':'PASS','sanity_and_negative_controls':'PASS'},
 'fidelity_verdict':'PASS','novelty_verdict':'HOLD','significance_verdict':'QUALIFIED_PASS',
 'significance_conditional_on_novelty':True,'recommendation':'HOLD; preserve completed certificate without campaign credit',
 'credit':0,'campaign_count':'5/20 beyond 39; unchanged',
 'formal':{'modules':11,'sigma_declarations':sum(n for m,n in summary['by_module'].items() if m.startswith('Sigma.')),'all_audited_declarations':len(rows),'allowed_axioms':summary['axioms'],'endpoint_names':['Sigma365710.extremal_completeBipartite','Sigma365710.attainer_classification','Sigma365710.mathdb_365710'],'source_definition':'arXiv:2411.04881v1 Eq. (4), unordered all-pair squared actual-degree differences','counter_checks':['P4=4','K1,3=12','K2,2=0','singleton=0','F(4,3)=12, Nat-subtraction analogue=0','DecidableRel instance independence'],'rejected_controls':['ordered total 8 for P4','edge-only total 2 for P4','balanced K2,2 dominates K1,3']},
 'bodies_read':[
 {'work':'Caro–Yuster 2000, Graphs with Large Variance','extent':'all 12 scanned pages 151–162, including proofs','finding':'Unrestricted fixed-edge and all-order maxima; no triangle-free maximum or strict Zagreb gap','receipt':'receipts/caro-body.pdf.json'},
 {'work':'Snijders 1981, The Degree Variance','extent':'journal pp.163–169 visually, all Section 3 maximum-value statements','finding':'Bipartite variance is one-part-only; undirected maxima unrestricted','receipt':'receipts/snijders.pdf.json'},
 {'work':'Snijders TW-229, April 1981','extent':'cover and printed pp.1–3 only; rest unread','finding':'Unrestricted majorization switch, no triangle-free-preservation premise','receipt':'receipts/snijders-proof.pdf.json'},
 {'work':'Zhou 2004 Zagreb indices','extent':'all six cached page images','finding':'Theorem 5 M1<=nm and Eq.1 deficit identity are old; n-2 gap absent'},
 {'work':'Filipovski et al. arXiv:2411.04881v1','extent':'Eq.4, Proposition1, triangle-free Section3.1, Props10–11 proofs, Conjecture24','finding':'Matches requested endpoints'},
 {'work':'Filipovski et al. 2026 journal successor','extent':'Caro–Yuster discussion in Section3; Conjecture6.1 and references','finding':'Still open in published source; supporting evidence, not novelty clearance'},
 {'work':'Filipovski 2024 A refined Turán theorem','extent':'all extracted theorem/proof body and references','finding':'Refines m bounds, including variance of squared degrees; no full target bridge found','receipt':'receipts/refined-turan.pdf.json'},
 {'work':'A general framework for inequalities on simple graphs, arXiv:2606.17356','extent':'relevant Sections3.2–3.3 and Theorem4.7/Corollaries4.8–4.9 with proofs','finding':'Spectral/closed-walk bounds, no target maximum or n-2 deficit','receipt':'receipts/framework.pdf.json'}],
 'bodies_unread':[
 {'work':'Bell 1992 A note on the irregularity of graphs','reason':'Publisher denied route not retried; distinct CORE PDF returned403, not retried'},
 {'work':'Réti 2019','reason':'OpenAlex locations only; ResearchGate403, not retried'},
 {'work':'Dimitrov–Stevanović 2023','reason':'No public body located; search challenge, not retried'},
 {'work':'Snijders journal pp.170–174 and TW-229 remainder','reason':'Downloaded but unread; no whole-body clearance asserted'},
 {'work':'Remaining strict Zagreb-gap and later-citing literature','reason':'Bounded queries and zero OpenAlex citing records do not clear full text'}],
 'objections':[
 {'id':'N1','gate':'B','severity':'blocking','description':'Bell body remains unread and is cited by Zhou for stronger squared-degree results; cannot exclude a subsumer'},
 {'id':'N2','gate':'B','severity':'blocking','description':'Réti, Dimitrov–Stevanović and specialist strict Zagreb-gap literature remain uncleared for nm-M1>=n-2 or equivalent variance extremum'},
 {'id':'N3','gate':'B','severity':'limitation','description':'Later-citing and registry screening is bounded; OpenAI recursive tree is truncated'}],
 'novelty_comparison':'Caro–Yuster full body does not resolve restricted maximum. Its Lemma2.5 switch creates a triangle on C5. Snijders bipartite result concerns one side. Zhou deficit identity is already known. Novelty of strict gap not established.',
 'live_registries':{'head_route':'GitHub /commits/HEAD','openai':'4eaee87548250b2682affda7d05d947c05554bae','omega':'8824ef07e683ac10ae019a2a355bc08dedac4985','omega_advanced_since_previous_review':True,'scope':'Path keywords and one nearby triangle-free problem body; no semantic exhaustive clearance','screens':['logs/openai-tree-screen.json','logs/omega-D5-screen.json','logs/omega-Problems-screen.json']},
 'limitations':['Prescribed upstream cache trusted; no independent mathlib rebuild','No separate arbitrary-vertex relabelling theorem in packet; binding target was Fin n and semantic invariance checked','Initial orientation source reads preceded before-hash baseline, disclosed in REVIEW.md','OCR executable unavailable; old scanned PDFs read as rendered images','Missing material bodies prevent novelty PASS'],
 'next_actions':['Read Bell through a distinct lawful institutional copy or root-provided lawful body','Read Réti and Dimitrov–Stevanović actual bodies','Search equivalent strict Zagreb deficit / induced-one-edge triple lower bounds and later citing full texts','Root independently adjudicates; do not count on technical PASS alone'],
 'preservation':{'input_trees_unchanged':not changes,'hash_receipts':['receipts/before.json','receipts/after.json'],'no_git':True,'no_shared_edits':True,'no_child_agents':True,'no_browser_tabs':True,'no_external_messages_publication_or_upload':True,'no_background_jobs_at_handback':True},
 'artifacts':{'report':'REVIEW.md','audit':'logs/declarations.jsonl','audit_summary':'receipts/audit-summary.json','driver':'scripts/rebuild.py','extraction':'scripts/extract.py','metrics':'receipts/validation-summary.json'}
}
(R/'review.json').write_text(json.dumps({'365710':v},indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'audit':summary,'preservation_files':len(after),'metrics':metrics},indent=2))
