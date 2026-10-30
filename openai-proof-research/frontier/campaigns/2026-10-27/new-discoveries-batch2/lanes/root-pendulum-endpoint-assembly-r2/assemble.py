from pathlib import Path
import hashlib,json,shutil,subprocess,sys,re
P=Path(__file__).resolve().parent;D=P/'extracted';E=P.parent/'sol-pendulum-endpoint-transfer-formal-r2';C=P.parent/'sol-pendulum-convex-series-formal-r2'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
receipt=json.loads((D/'replay-receipt.json').read_text());assert receipt['declaration_count']==88 and receipt['status']=='MANDATORY_COMPONENT_SOURCE_ONLY_REPLAY_PASS'
for root in [P,P.parent/'root-pendulum-convex-series-adoption-r2']:
 for r in json.loads((root/'review-freeze.json').read_text())['files']:
  p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
for name in ['Defs','Substitution','Moments','Source']:assert (D/'formal'/f'{name}.lean').read_bytes()==(C/'formal'/f'{name}.lean').read_bytes()
for name in ['Convexity','Series']:shutil.copyfile(C/'formal'/f'{name}.lean',D/'formal'/f'{name}.lean')
source='''module
public import Series
public import EndpointTransfer
public section
noncomputable section
namespace PendulumTimeMap
theorem source_claim : SourceClaim :=
  sourceClaim_of_interior_convex (fun _ hp hp2 => sourceTime_interior_convex hp hp2)
end PendulumTimeMap
'''
(P/'Result.lean').write_text(source);(D/'formal/Result.lean').write_text(source)
audit=(E/'formal/FullAudit.lean').read_text().replace('import Lean','import all Convexity\nimport all Series\nimport all Result\nimport Lean').replace('`EndpointTransfer]','`EndpointTransfer, `Convexity, `Series, `Result]')
assert audit!=(E/'formal/FullAudit.lean').read_text()
(D/'formal/CombinedAudit.lean').write_text(audit)
steps=[]
for name in ['Convexity','Series','Result','CombinedAudit']:
 p=subprocess.run([sys.executable,str(D/'guard.py'),name],capture_output=True,text=True)
 print(p.stdout,flush=True);assert p.returncode==0,p.stderr
 steps.append(json.loads((D/'logs'/f'{name}.json').read_text()))
 if name!='CombinedAudit':assert (D/'logs'/f'{name}.log').stat().st_size==0
s=(D/'logs/CombinedAudit.log').read_text()
rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',s,re.M|re.S)
assert len(rows)==int(re.search(r'AUDIT_TOTAL (\d+)',s)[1])==139
out=[]
for mod,name,t,axs,u,p,a in rows:
 aa=re.findall(r'[\w.]+',axs);assert set(aa)<={'propext','Classical.choice','Quot.sound'} and (u,p,a)==('false','false','false')
 out.append({'origin':mod,'name':name,'actual_type':t,'axioms':aa,'unsafe':False,'partial':False,'axiom':False})
assert len({r['name'] for r in out})==139 and len({r['origin'] for r in out})==14
for base in [E,C]:
 old=json.loads((base/'actual-declarations.json').read_text());table={r['name']:r for r in out}
 for r in old:assert table[r['name']]==r,r['name']
endpoint=[r for r in out if r['name']=='PendulumTimeMap.source_claim'];assert len(endpoint)==1 and endpoint[0]['actual_type']=='PendulumTimeMap.SourceClaim',endpoint
(P/'combined-actual-declarations.json').write_text(json.dumps(out,indent=2)+'\n')
sys.path.insert(0,str(D));import audit_tools
audit_tools.MODS+=['Convexity','Series','Result']
deps=audit_tools.dependencies(D);(P/'combined-dependency-hashes.json').write_text(json.dumps(deps,indent=2)+'\n')
for r in json.loads((P/'review-freeze.json').read_text())['files']:assert sha(Path(r['path']))==r['sha256']
final={'status':'PASS','root_endpoint_fresh_replay':True,'endpoint_declarations':88,'combined_mathematical_modules':14,'combined_actual_declarations':139,'unconditional_source_claim':endpoint[0],'both_components_actual_rows_unchanged':True,'combined_dependency_files':len(deps),'steps':steps,'fresh_merged_packet_replay_pending':True,'credit':0}
(P/'verification-receipt.json').write_text(json.dumps(final,indent=2)+'\n');print('UNCONDITIONAL SOURCE CLAIM PASS; 14 modules /139 declarations; merged packet replay pending')
