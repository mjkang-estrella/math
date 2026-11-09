"""Read-only independent verifier; stdout receipt, nonzero on any mismatch."""
from pathlib import Path
import hashlib,json,sys,datetime
L=Path(__file__).resolve().parent;B=L.parent;R=B/'root-mathdb-breadth-intake-r403';C=B/'pi-mathdb-full-corpus-inventory-r301'
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert digest(b)==e['sha256'],('hash',str(p))
def canon(r):return json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':'))
try:
 # Flat immutable refs, including actual originals, not copies substituted for originals.
 refs=json.loads((L/'bindings.json').read_text())['refs']
 for p,e in refs.items():check(Path(p),e)
 for e in json.loads((R/'manifest.json').read_text())['files']:check(R/e['path'],e)
 for e in json.loads((R/'bindings.json').read_text()):check(Path(e['original']),e)
 cm=json.loads((C/'manifest.json').read_text()); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
 for e in chunks:check(C/e['path'],e)
 a=json.loads((R/'reserved-ids.json').read_text());A=set(a['ids']);other=set(a['other_active_reservations']);old=set(map(int,json.loads((R/'coverage-delta.json').read_text())))
 assert a['lane']==L.name and len(a['ids'])==len(A)==50 and len(other)==50 and len(old)==1483
 assert not A&(other|old|{372627,372628,368940})
 assert A=={r['mathdb_id'] for r in json.loads((R/'queue.json').read_text())}
 ds=json.loads((L/'dispositions.json').read_text());rs=json.loads((L/'records.json').read_text());assert len(ds)==len(rs)==50
 assert {r['mathdb_id'] for r in ds}=={r['mathdb_id'] for r in rs}==A
 d={r['mathdb_id']:r for r in ds};stored={r['mathdb_id']:r for r in rs};seen=set()
 # Parse only after every corpus chunk has been verified in place.
 for e in chunks:
  for n,line in enumerate((C/e['path']).open(),1):
   r=json.loads(line);i=r['mathdb_id']
   if i not in A:continue
   assert i not in seen;seen.add(i);x=d[i];s=r['statement'];assert r['statement_completeness']=='full'
   assert x['literal_statement']==s and x['statement_sha256']==digest(s.encode())
   assert x['canonical_statement_sha256']==digest(' '.join(s.split()).encode())
   assert x['canonical_record_sha256']==digest(canon(r).encode())
   assert x['canonical_url']==r['canonical_url'] and x['source_url']==r['source_url']
   assert stored[i]==dict(r,corpus_ref={'path':str(C/e['path']),'line':n})
   assert x['corpus_ref']==stored[i]['corpus_ref'] and x['credit']==0 and x['literal_review']
   assert x['exact_scope'] and x['reason'] and not x['complete_dependency_audit']
 assert seen==A
 assert json.loads((L/'proposals.json').read_text())==[]
 for e in json.loads((L/'source-provenance.json').read_text()):
  if 'sha256' in e:check(L/e['file'],e)
 manifest=json.loads((L/'manifest.json').read_text());paths={e['path'] for e in manifest['files']};assert len(paths)==len(manifest['files'])
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','finalreceipt.json']}
 assert paths==actual,('payloadset',sorted(paths^actual))
 for e in manifest['files']:check(L/e['path'],e)
 out={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bound_originals_and_inputs':len(refs),'root_manifest_read_only':True,'corpus_chunks_verified_in_place_before_parse':20,'exact_assigned_statements':50,'prior_reviewed_count':1483,'active_other_reservations':50,'assignment_exactset_and_disjoint':True,'literal_canonical_record_hashes':True,'payload_exactset':True,'payload_count':len(paths),'qualified_proposals':0,'credit':0,'current_registry':'HOLD'}
 print(json.dumps(out,indent=2))
except Exception as ex:
 print(json.dumps({'status':'FAIL','error':repr(ex)}));sys.exit(1)
