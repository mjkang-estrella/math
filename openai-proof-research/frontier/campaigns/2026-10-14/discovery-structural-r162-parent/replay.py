#!/usr/bin/env python3
"""Authenticate the failed Structural162 discovery, without a mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r162'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'ccf10954168f7d30d0153bdd55510c3e5eae86f5ef28f7f2ff1c698156c8ff60','MANIFEST.json':'c05a9b5867f5d69f2e151bb1fdac43110e3f6cd1557806a4993c78efdf6772ae','REPORT.md':'0aec0ece3b5fbef03e2ab6cddbcc68b7ab8c953ebec25e2e55cdb63eea9d84af'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'];assert len(read(B/'tasks.json')['tasks'])==548
 before=snap(ROOT);m=read(ROOT/'MANIFEST.json');assert len(m['files'])==18 and len(m['directories'])==4
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():
  q=ROOT/n;assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and oct(stat.S_IMODE(q.stat().st_mode))==e['mode'] and q.stat().st_nlink==1
 stable=[]
 for e in read(ROOT/'private/incoming-original-identities.json'):
  q=P/e['incoming_original'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and oct(stat.S_IMODE(q.stat().st_mode))==e['mode'] and e['selected_copy'] is None;stable.append({'path':e['incoming_original'],'bytes':e['size'],'sha256':e['sha256'],'mode':e['mode']})
 assert len(stable)==11;tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated']
 ctl=read(ROOT/'private/copied-control-results.json');assert sha(P/ctl['incoming_original'])==ctl['incoming_sha256']==sha(ROOT/ctl['selected_copy']) and len(ctl['cases'])==6 and all(e['expected_behavior'] for e in ctl['cases'])
 cases=[]
 with tempfile.TemporaryDirectory(prefix='structural162-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);initial=snap(copy)
  args=[str(copy),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'unchanged':True})
  check('unchanged',True);q=copy/'notes/01-selection-and-mathematical-stop.md';data=q.read_bytes();q.write_bytes(data+b'CONTROL');check('changed_member',False);q.unlink();check('missing_member',False);q.write_bytes(data);q.chmod(initial[str(q.relative_to(copy))]['mode']);q=copy/'.extra';q.write_text('extra');check('unexpected_member',False);q.unlink();args2=args.copy();args2[2]='0'*64;check('wrong_final_anchor',False,args2);q=copy/'empty';q.mkdir();check('unexpected_empty_directory',False);q.rmdir();q=copy/'notes/00-start.md';mode=q.stat().st_mode;q.chmod(0o600);check('changed_mode',False);q.chmod(stat.S_IMODE(mode));check('restored',True);assert snap(copy)==initial
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'limits':'Root-directory mode excluded.'});dump('copied-controls.json',{'cases':cases,'positive':2,'negative':6,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no mathematical gate.'});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':18,'whole_root_files':21,'subdirectories':4,'source_files':0,'primary_versions':0,'stable_named_originals':stable,'required_r161_identity_only_originals':7,'artifact_cases':8,'whole_actual_root_unchanged':True,'limits':'No source/primary was selected. No mathematical derivation, finite/formal experiment or independent gate.'})
 print(json.dumps({'payload':18,'files':21,'dirs':4,'stable_originals':11,'artifact_cases':8,'mathematical_gate':False}))
if __name__=='__main__':main()
