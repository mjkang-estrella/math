from pathlib import Path
import os,sys,json,hashlib,stat
ROOT=Path(__file__).resolve().parents[1]; PROJECT=ROOT.parents[3]; BASE=ROOT.parent
NAMES=['fresh-analytic-discovery-r133','t088p133-contribution-r1','t088p133-proof-r3','t088p133-formal-v1','t088p133-formal-review-r1','t088p133-manuscript-r1','t088p133-manuscript-r2','t088p133-manuscript-review-r1']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b)
 return h.hexdigest()
def snap(root):
 result={}
 for d,ds,fs in os.walk(root,followlinks=False):
  for n in sorted(ds+fs):
   p=Path(d)/n;s=p.lstat();v={'mode':stat.S_IMODE(s.st_mode),'kind':'dir' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'link','links':s.st_nlink if not stat.S_ISDIR(s.st_mode) else None}
   if stat.S_ISREG(s.st_mode):v.update(bytes=s.st_size,sha256=sha(p))
   elif stat.S_ISLNK(s.st_mode):v['target']=os.readlink(p)
   result[p.relative_to(root).as_posix()]=v
 return result
def package(name,anchors):
 r=BASE/name
 for p,h in zip(['FINAL.json','packet/MANIFEST.json','REPORT.md'],anchors):assert sha(r/p)==h,(name,p)
 m=json.loads((r/'packet/MANIFEST.json').read_text());f=json.loads((r/'FINAL.json').read_text())
 assert f['manifest_sha256']==anchors[1] and f['report_sha256']==anchors[2]
 for p,v in m['files'].items():
  q=r/p;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],p
  assert stat.S_IMODE(q.stat().st_mode)==v['mode'] and q.stat().st_nlink==1,p
 got=snap(r/'packet');assert {('packet/'+p) for p,v in got.items() if v['kind']=='file'}==set(m['files'])|{'packet/MANIFEST.json'}
 assert {'packet'}|{('packet/'+p) for p,v in got.items() if v['kind']=='dir'}==set(m['directories'])
 for p,v in m['directories'].items():assert stat.S_IMODE((r/p).stat().st_mode)==v['mode']
 return {'anchors':dict(zip(['final','manifest','report'],anchors)),'files':len(m['files']),'directories':len(m['directories'])}
def main():
 results={}
 results['r2']=package('t088p133-manuscript-r2',['7a98b6fc2f55ddc21187b77dac24538e193492732e36fe0f07fe4c5bf3c29672','c726a7a8329271f9a903cb88b230217820574f1c5e35248ed3670becacc68d68','11a45a886b1cba9262809a8cfce0df5842ead74993efb0730400ab4702bab6f1'])
 results['review']=package('t088p133-manuscript-review-r1',['4c184023e08b7713ef1204c1153cb4f663470e46358e664a8dd9ea8b08ff8aa9','0339b3229c63e11531066d6e06e752fb031a6476a207ad417bc98261fe1a7d07','3393e0d885ec1ba919b32ca3644d14ea471ed94a5f642f809fb7e49f741281ef'])
 r=BASE/'t088p133-manuscript-r2';f=json.loads((r/'FINAL.json').read_text())
 for rel,key in [('private/MANIFEST-r2.json','private_evidence_manifest_sha256'),('private/build-cache-manifest-r2.json','private_cache_inventory_sha256')]:
  assert sha(r/rel)==f[key]
  m=json.loads((r/rel).read_text())
  for p,v in m['files'].items():
   q=r/p;assert sha(q)==v['sha256'] and q.stat().st_size==v['bytes'] and stat.S_IMODE(q.stat().st_mode)==v['mode'],p
  results[rel]={'sha256':sha(r/rel),'named_files':len(m['files']),'public_verifier_coverage':False}
 tree=PROJECT/'sources/preprints-tree.json';assert sha(tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 t=json.loads(tree.read_text());assert len(t['tree'])==13223 and not t.get('truncated',False)
 results['tree']={'sha256':sha(tree),'entries':len(t['tree']),'upstream_truth_audit':False}
 o=json.loads((r/'packet/public/formal/origin.json').read_text());assert sha(r/'packet/public/formal/origin.json')=='992a50f40e09ed2a03eb124d93da5a55508e81373046f7b16d892364165344ea'
 for p,v in o.items():assert sha(r/'packet/public'/p)==v['sha256']
 results['formal_origin_files']=len(o)
 public=BASE/'fresh-analytic-discovery-r133/packet/public'
 for name,h in [('FROZEN-THEOREM.md','86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354'),('proof.md','971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84')]:assert sha(public/name)==h
 before=ROOT/'work/originals-before.json'
 if sys.argv[-1]=='before':
  inventory={n:snap(BASE/n) for n in NAMES};before.write_text(json.dumps(inventory,sort_keys=True)+'\n');results['original_entries']=sum(map(len,inventory.values()))
 else:
  old=json.loads(before.read_text());results['original_roots_unchanged']={n:snap(BASE/n)==old[n] for n in NAMES};assert all(results['original_roots_unchanged'].values())
 (ROOT/('work/input-audit-'+sys.argv[-1]+'.json')).write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
if __name__=='__main__':main()
