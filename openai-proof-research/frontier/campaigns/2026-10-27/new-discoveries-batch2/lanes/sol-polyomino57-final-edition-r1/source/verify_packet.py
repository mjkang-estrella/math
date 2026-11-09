"""Offline integrity/reproduction check. Does not claim to replace fresh Lean replay."""
from pathlib import Path
import resource,signal,os,sys,zipfile,json,hashlib,subprocess,re,platform,zlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
archive=Path(sys.argv[1]).resolve();work=Path(sys.argv[2]).resolve();work.mkdir();E=work/'extracted';E.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
with zipfile.ZipFile(archive) as z:
 for n in z.namelist():
  assert not Path(n).is_absolute() and '..' not in Path(n).parts
  assert Path(n).suffix not in ['.olean','.ilean','.so','.o','.pyc','.zip']
 assert len(z.namelist())==len(set(z.namelist()))
 z.extractall(E)
mf=json.loads((E/'MANIFEST.json').read_text())
assert set(mf)=={str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
for n,v in mf.items():assert sha(E/n)==v['sha256'] and (E/n).stat().st_size==v['bytes'],n
sources=json.loads((E/'source-manifest.json').read_text());mods=json.loads((E/'consumed-modules.json').read_text());assert len(sources)==2023 and len(mods)==2022
assert set(sources)=={'formal/'+m+'.lean' for m in mods+['FinalAudit']}
assert {p.name for p in (E/'formal').iterdir()}=={m+'.lean' for m in mods+['FinalAudit']}
seen=set()
for m in mods+['FinalAudit']:
 p=E/'formal'/(m+'.lean');assert sha(p)==sources[str(p.relative_to(E))]['sha256']
 s=p.read_text()
 if m!='FinalAudit':assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s),m
 for im in re.findall(r'^import (\S+)',s,re.M):
  if im in mods:assert im in seen,(m,im)
 seen.add(m)
closure=set()
def visit(m):
 if m in closure:return
 closure.add(m)
 for im in re.findall(r'^import (\S+)',(E/'formal'/(m+'.lean')).read_text(),re.M):
  if (E/'formal'/(im+'.lean')).exists():visit(im)
visit('AllCases')
assert closure==set(mods),'exact consumed mathematical dependency closure'
receipt=json.loads((E/'replay-evidence/REPLAY-RECEIPT.json').read_text());assert receipt['status']=='PASS' and receipt['modules']==2022 and receipt['declarations']==5924
assert receipt['source_manifest_sha256']==sha(E/'source-manifest.json')
assert len(receipt['build_reports'])==2024
assert all(r['rc']==0 and r['kill_reason'] is None and r['peak_group_rss']<2800*1024**2 and r['seconds']<230 and r['interval_seconds']==.045 for r in receipt['build_reports'])
inv=json.loads((E/'replay-evidence/declaration-inventory.json').read_text());old=json.loads((E/'inherited/declaration-inventory.json').read_text())
assert len(inv)==len({v['name'] for v in inv})==5924
assert {v['name']:v for v in inv}=={v['name']:v for v in old},'all actual types/origins/axioms/flags must match frozen inventory'
for v in inv:
 assert v['origin'] in mods and v['type']
 assert v['flags']==('unsafe=false partial=true axiom=false' if v['name']=='Polyomino57.attachCheck._unsafe_rec' else 'unsafe=false partial=false axiom=false')
 assert set(re.findall(r'[A-Za-z][A-Za-z.]*',v['axioms']))<=set(['propext','Classical.choice','Quot.sound'])
assert receipt['pins']==json.loads((E/'pins.json').read_text())
blocks=re.findall(r'AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS ([^\n]+)',(E/'replay-evidence/logs/FinalAudit.log').read_text(),re.S)
actual=[dict(origin=o,name=n,type=t,axioms=a,flags=f) for o,n,t,a,f in blocks]
assert actual==inv and len(actual)==5924
assert set((E/'replay-evidence/declaration-names.txt').read_text().splitlines())=={v['name'] for v in inv}
# Final edition exact evidence binding; no new Lean run is implied.
evidence=json.loads((E/'PROVENANCE.json').read_text())['final_edition_evidence']
for v in evidence:
 p=E/v['packet_path'];assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes']
for lane,receipt_name,inventory_name in [
 ('root-polyomino57-final-review-freeze-r1','ROOT-REPLAY-RECEIPT.json','root-fresh-replay/declaration-inventory.json'),
 ('sol-polyomino57-full-final-review-r1','fresh-replay/REPLAY-RECEIPT.json','fresh-replay/declaration-inventory.json')]:
 d=E/'evidence'/lane;r=json.loads((d/receipt_name).read_text())
 assert r['status']=='PASS' and r['modules']==2022 and r['declarations']==5924
 assert r['source_manifest_sha256']==sha(E/'source-manifest.json')
 assert sha(d/inventory_name)=='bb24a892d49115ba1538de2994a2452088cad156d091ed69fa960f09cb50e4c9'
 assert json.loads((d/inventory_name).read_text())==inv
 log=d/('root-fresh-replay/logs/FinalAudit.log' if lane.startswith('root-') else 'fresh-replay/logs/FinalAudit.log')
 b=re.findall(r'AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS ([^\n]+)',log.read_text(),re.S)
 assert [dict(origin=o,name=n,type=t,axioms=a,flags=f) for o,n,t,a,f in b]==inv
pdfhash=sha(E/'paper.pdf')
subprocess.run([sys.executable,str(E/'build_pdf.py')],check=True,timeout=230)
assert sha(E/'paper.pdf')==pdfhash,'PDF byte identity'
rebuilt=work/'rebuilt.zip'
subprocess.run([sys.executable,str(E/'pack.py'),str(rebuilt)],check=True,timeout=230)
assert sha(rebuilt)==sha(archive),'ZIP byte identity'
result=dict(status='PASS',packet_sha256=sha(archive),paper_sha256=pdfhash,entries=len(mf)+1,formal_entries=2023,modules=2022,declarations=5924,all_actual_records_match_frozen_inventory=True,PDF_byte_identical=True,ZIP_byte_identical=True,from_extraction=True,python=platform.python_version(),zlib=zlib.ZLIB_RUNTIME_VERSION,credit=0,root_acceptance=False)
(work/'REPRODUCTION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
