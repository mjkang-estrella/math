import json,pathlib,hashlib,re,datetime,collections
L=pathlib.Path(__file__).resolve().parent
rows=json.loads((L/'assigned-records.json').read_text());ass={int(a):[b,c] for a,b,c in (line.split('\t',2) for line in (L/'assessment.tsv').read_text().splitlines())};assert len(ass)==50
sources=json.loads((L/'source-receipts.json').read_text());assert len(sources)==50
catalog=[]
for r in sources+json.loads((L/'successor-receipts.json').read_text()):
 q=dict(r)
 if 'path' in r:
  s=pathlib.Path(r['path']).with_suffix('.txt').read_text();m=re.search(r'arXiv:([^\s]+)',s);q['observed_body_version']=m.group(1) if m else 'not extracted';q['read_level']='selected passages; no whole-body/dependency audit'
 catalog.append(q)
(L/'source-catalogue.json').write_text(json.dumps(catalog,indent=2)+'\n')
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];status,mechanism=ass[i];src=next(s for s in catalog if s.get('id')==i)
 out.append(dict(mathdb_id=i,title=r['title'],literal_statement=r['statement'],statement_sha256=x['statement_sha256'],canonical_record_sha256=x['canonical_record_sha256'],original_chunk=x['original_chunk'],original_line=x['original_line'],source_url=r['source_url'],source_name=r['source_name'],disposition=status,technical_assessment=mechanism,statement_review='literal statement and quantifiers read',primary_level='selected question/context passages inspected; extracted locator may be a mention rather than the question; see supplement and gaps',source_body_retained=src['path'],source_body_sha256=src['sha256'],source_body_version=src['observed_body_version'],whole_body_read=False,dependency_audit=False,proof_level='No new complete proof; public theorem reports distinguished from audited proofs',registry_level='HOLD: current public registry heads and chronology not cleared; no novelty inferred from search absence',successor_level='Theorem passage inspected' if i in {322219,323515,323760,323822} else 'Incomplete; internal results inspected where stated, closest successor not fully audited',bounded_check='Executed exhaustive F2^4 subspace orbit enumeration: 67 spaces, 36 actions, ten nonzero orbits. Scope limited; see bounded-checks.json' if i==323693 else 'No target computation executed; proposed tests in technical assessment are planned only',certificate_size='67 subspaces and ten orbit representatives for the limited check; full rank/table certificate absent' if i==323693 else 'No full-scope certificate produced',formal_dependencies='Finite-field linear algebra and finite group actions; rank invariance and lexicographic Table 5 comparison remain' if i==323693 else 'Subject-specific definitions and theorems in the cited primary source; no Lean endpoint or dependency audit supplied',strongest_objection=mechanism,prior_gaps='Current proof-registry clearance absent; source/closest-successor dependency audits incomplete. Public resolutions receive no credit.',eligible_proposal=False))
(L/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(L/'proposals.json').write_text('[]\n')
print('counts',dict(collections.Counter(x['disposition'] for x in out)))
a=json.loads((L.parent/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json').read_text());print('accepted families',[(x.get('family_id'),x.get('title',x.get('name'))) for x in a['families']][:45])
