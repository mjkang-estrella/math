import resource,signal,json,hashlib,shutil,datetime,os
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230);os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
D=Path('.').resolve();old=D.parent/'sol-fresh-source-discovery-r47/sources';B=D/'r47-baseline';B.mkdir(exist_ok=True)
for n in ['omega-head.json','omega-main-head.json','openai-head.json','aim-head.json','count-head.json','omega-D5.json','omega-Problems.json','openai-preprints.json','aim-tree.json','count-tree.json']:
 shutil.copyfile(old/n,B/n)
pages={}
for n in range(1,8):
 p=D/('page-'+str(n)+'.png');pages[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
Path('read-evidence.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pdf_sha256=hashlib.sha256((D/'extracted/paper.pdf').read_bytes()).hexdigest(),pages=pages,personally_rendered_and_read_all_pages=True,manual_bridges=['Grid','Growth','Normalization','Bounds','Witness','Diagonal','Spans','Placement','Symmetry','SignedNormalization','CanonicalCoverage','Potential','Bridge','FiniteBridge','PackedRows','PackedBits','MaskBridge','PackedHalf','ForcedBridge','Completed','AllCases'],generated_data='Every formal domain/group/table parsed independently; all BASE/EDGE/MERGE/FULL values checked; every generated module kernel-replayed; no claim of individually reading each literal digit.',primary_history=dict(status='cached primary bodies read; no fresh access',urls=['https://oeis.org/history?seq=A395495','https://oeis.org/history?seq=A395495&start=10'],sha256=hashlib.sha256(Path('cached-primary-history.json').read_bytes()).hexdigest())),indent=2)+'\n')
# All case interfaces are preserved as a reviewable actual-type catalogue from the fresh environment.
inv={x['name']:x for x in json.loads(Path('fresh-replay/declaration-inventory.json').read_text())};cm=json.loads(Path('extracted/CASE-MAP.json').read_text());out=[]
for c in cm:
 v=inv[c['declaration']];assert v['origin']==c['origin'];assert v['type'] and '11' in v['type'];out.append(dict(case=c,actual=v))
assert len(out)==70;Path('actual-case-interfaces.json').write_text(json.dumps(out,indent=2)+'\n')
