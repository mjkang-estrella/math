from pathlib import Path
import json,hashlib,shutil,subprocess,sys,os
R=Path.cwd();F=R/'private/controls-fixture';P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
assert not F.exists();F.mkdir()
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(rel):
 q=F/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/rel,q)
def snap(root):
 files={};dirs=[]
 for base,ds,fs in os.walk(root):
  dirs.extend(str((Path(base)/x).relative_to(root)) for x in ds)
  for x in fs:
   p=Path(base)/x;files[str(p.relative_to(root))]=sha(p.read_bytes())
 return {'files':files,'directories':sorted(dirs)}
def originals():return {r['path']:sha((P/r['path']).read_bytes()) for r in json.loads((R/'original-authentication.json').read_bytes())}
external_before=originals(); protected=[r['local'] for r in json.loads((R/'source-authentication.json').read_bytes())]
protected += [r['raw'] for r in json.loads((R/'primary-authentication.json').read_bytes())]
protected += [r['local'] for r in json.loads((R/'selected-copy-membership.json').read_bytes())]
own_before={p:sha((R/p).read_bytes()) for p in protected}
copy('verify.py');copy('DERIVATION.md');copy('private/preprints-tree.json')
src=json.loads((R/'source-authentication.json').read_bytes())
src=[next(r for r in src if r['path'].endswith('01-introduction.tex'))]
copy(src[0]['local']);(F/'source-authentication.json').write_text(json.dumps(src,indent=2)+'\n')
pr=[next(r for r in json.loads((R/'primary-authentication.json').read_bytes()) if r['name']=='bizeul')]
copy(pr[0]['raw'])
for m in pr[0]['members']:copy(m['local'])
(F/'primary-authentication.json').write_text(json.dumps(pr,indent=2)+'\n')
orig=[next(r for r in json.loads((R/'original-authentication.json').read_bytes()) if r['path'].endswith('r83/working-transport.md'))]
sel=[r for r in json.loads((R/'selected-copy-membership.json').read_bytes()) if r['original_id']==orig[0]['id']]
copy(sel[0]['local']);(F/'original-authentication.json').write_text(json.dumps(orig,indent=2)+'\n');(F/'selected-copy-membership.json').write_text(json.dumps(sel,indent=2)+'\n')
(F/'FINAL.md').write_text('Reduced copied control fixture; not a research conclusion.\n')
(F/'REPORT.md').write_text('Own manifest generated from actual selected-copy membership. No original manifest imported.\n')
ss=snap(F);files=[]
for rel in sorted(ss['files']):
 if rel in {'FINAL.md','REPORT.md','MANIFEST.json'}:continue
 b=(F/rel).read_bytes();files.append({'path':rel,'size':len(b),'sha256':sha(b)})
(F/'MANIFEST.json').write_text(json.dumps({'outside_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'directories':ss['directories'],'files':files},indent=2)+'\n')
anchors={n:sha((F/(n.upper()+'.md' if n!='manifest' else 'MANIFEST.json')).read_bytes()) for n in ['final','manifest','report']}
base=snap(F);results=[]
def run(name,want,override=None):
 before=snap(F);aa=dict(anchors);aa.update(override or {});cmd=[sys.executable,str(F/'verify.py'),str(F),'--project',str(P)]
 for n,h in aa.items():cmd += ['--'+n+'-sha',h]
 r=subprocess.run(cmd,capture_output=True,text=True,timeout=30);after=snap(F)
 assert before==after,'verifier wrote during '+name
 assert (r.returncode==0)==want,(name,r.stdout,r.stderr)
 results.append({'name':name,'expected_accept':want,'exit_code':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'read_only_snapshot_unchanged':True})
run('baseline',True)
p=F/src[0]['local'];b=p.read_bytes();p.write_bytes(b+b'\nMUTATED\n');run('changed-source-copy',False);p.write_bytes(b)
p=F/'DERIVATION.md';b=p.read_bytes();p.unlink();run('missing-payload',False);p.write_bytes(b)
p=F/'.hidden-extra';p.write_text('unexpected\n');run('hidden-extra',False);p.unlink()
run('wrong-detached-manifest-anchor',False,{'manifest':'0'*64})
assert snap(F)==base;run('restored',True)
assert originals()==external_before,'external originals changed during controls'
assert {p:sha((R/p).read_bytes()) for p in protected}==own_before,'protected owned originals changed'
rec={'artifact_only':True,'fixture_own_manifest':True,'original_manifest_imported':False,'fixture_baseline_manifest_sha256':anchors['manifest'],'fixture_selected_payload_files':len(files),'results':results,'external_originals_observed_unchanged':len(external_before),'protected_owned_files_observed_unchanged':len(protected),'fixture_removed_after_checks':True}
shutil.rmtree(F)
(R/'controls.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({'controls':len(results),'expected_outcomes_met':True,'external_originals_unchanged':len(external_before),'fixture_removed':True}))
