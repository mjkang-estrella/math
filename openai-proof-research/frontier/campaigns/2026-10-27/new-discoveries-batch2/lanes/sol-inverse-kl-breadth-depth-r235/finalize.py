from pathlib import Path
import hashlib,json,datetime,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'frozenbindings.json').read_text())
after=[]
for r in bindings:
 a=h(Path(r['original']));b=h(Path(r['copy']))
 after.append({'original':r['original'],'original_after':a,'copy_after':b,'expected':r['sha256'],'pass':a==b==r['sha256']})
assert all(r['pass'] for r in after)
(L/'source-after.json').write_text(json.dumps(after,indent=2))
ns={'a':'http://www.w3.org/2005/Atom'};meta=[]
for filename in ['breadth.xml','triangulations-status.xml']:
 for e in E.parse(L/'primary'/filename).findall('a:entry',ns):
  meta.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
(L/'source-chronology.json').write_text(json.dumps(meta,indent=2))
prov={'lane':str(L),'status':'NO FULL SOURCE RESULT; inverse-KL public refutation; all-ear triangulations unresolved','credit':0,'counts':{'additional':9,'total':39,'next':40},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','caps':{'address_space_bytes':536870912,'group_rss_bytes':536870912,'cpu_seconds':210,'wall_seconds':230,'raised':False},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'scientific_freeze':'frozenbindings.json and retrieval.jsonl; downloaded bytes hashed/read-only before pdftotext; extracted text read-only and hashed before scientific reading','administrative':'administrative copies are point-in-time snapshots, not immutable scientific source originals','immutable_reuse':'compact root reports bound by hash; no recursive historical trees copied','history_reports_bound':len(json.loads((L/'history-bindings.json').read_text())),'source_originals_copies_pass':all(r['pass'] for r in after),'registry':'HOLD; inherited forbidden routes not retried; historical intervals parked','ordinary_result':False,'lean':False,'manuscript':False,'children':False,'external_mutations':False,'source_attribution_limit':'several breadth original historical bodies unread; explicit in SCOUTING','failures':'FAILURES.md and retrieval.jsonl'}
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
excluded={'finalmanifest.json','verification-receipt.json'}
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
(L/'finalmanifest.json').write_text(json.dumps(manifest,indent=2));print('manifest files',len(manifest),'frozen source bindings',len(bindings))
