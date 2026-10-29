from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent
http=[json.loads(l) for l in (P/'http.jsonl').read_text().splitlines()]
source=[{'path':str(f.relative_to(P)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size} for f in sorted((P/'sources').iterdir()) if f.is_file()]
(P/'provenance.json').write_text(json.dumps({'lane':'sol-fresh-source-discovery-r59','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'credit':0,'root_counts_unchanged':{'additional':6,'total':36},'status':'unresolved full substantive real-rootedness; no nomination','source_requests':http,'source_files':source,'registry_freshness':'HOLD: inherited four shared API403; no API requests this lane','registry_baseline':'r57 complete named Blueprint/D5 and Problems at3b4135a35caa0ae817cf5eca51d605b098027fd2; latest known head6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3 from r58','source_versions':{'selected_initial':'2410.00127v2 Conjecture6.1','selected_latest':'2410.00127v3 2026-06-30; Conj6.1 omitted','closest_recurrence':'2607.00922v1 Proposition3.2','closest_generalized_snake':'2607.00922v1 Theorem4.1','excluded_prior':'2605.29151v1 and latestv2 2026-06-11 Theorem1.1','classical':'math/0303147 preprintTheorem16; publisherTheorem17 body inaccessible403'},'novelty_pass':False,'limits':{'AS_MiB':512,'sampled_group_RSS_MiB':512,'CPU_s':210,'wall_s':230,'BLAS_threads':1},'protocol_deviations':['Two preliminary Python metadata/parser snippets ran without the wrapper: one cached-tree filter and one missing-bs4 parser import. Neither was mathematical experimentation; disclosed in failures.md. Subsequent helper, fetch and check processes capped.'],'external_mutation':False,'children':False,'git_actions':False,'proof_md':False,'lean_or_paper':False},indent=2)+'\n')
# Keep read evidence directly tied to local source files, not search snippets.
from parse import Parser
for name in ['acm-proof-v2','rook-v3','snake','ajq']:
 f=P/'sources'/(name+'.html');p=Parser();p.feed(f.read_text());f.with_suffix('.txt').write_text(' '.join(' '.join(p.out).split()))
extracts={}
for name,terms in {'rook':['Conjecture 6.1'], 'rook-v3':['Theorem 4.1','Theorem 4.3'], 'snake':['Proposition 3.2','Theorem 4.1'], 'acm-proof-v2':['Theorem 1.1','4. Proof of real-rootedness'], 'ajq':['Conjecture 28']}.items():
 txt=(P/'sources'/(name+'.txt')).read_text();extracts[name]=[]
 for term in terms:
  # later occurrence avoids table of contents where applicable
  idx=txt.find(term)
  extracts[name].append({'label':term,'offset':idx,'excerpt':txt[idx:idx+2500]})
(P/'source-extracts.json').write_text(json.dumps(extracts,indent=2)+'\n')
f=P/'provenance.json';d=json.loads(f.read_text())
d['source_files']=[{'path':str(q.relative_to(P)),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size} for q in sorted((P/'sources').iterdir()) if q.is_file()]
f.write_text(json.dumps(d,indent=2)+'\n')
print('saved provenance and source read anchors')
