"""Build a small copied fixture and verify fail-closed/read-only behavior."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,os
root=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r156')
ns={'__name__':'verifier_library'};exec((root/'original/verify.py').read_text(),ns)
base=root/'private/copied-controls';base.mkdir(exist_ok=True);fixture=base/'fixture';fixture.mkdir()
shutil.copyfile(root/'notes/01-prefreeze-calculations.md',fixture/'note.md')
shutil.copyfile(root/'original/subgroup_diagnostic.py',fixture/'diagnostic.py')
shutil.copyfile(root/'original/verify.py',fixture/'verify.py')
inv=ns['inventory'](fixture);manifest={'schema':1,**inv}
(fixture/'MANIFEST.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
(fixture/'FINAL.md').write_text('Copied-control fixture only; no mathematical gate.\n')
(fixture/'REPORT.md').write_text('Own fixture membership, no inherited whole-original manifest.\n')
anchors=[ns['digest'](fixture/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']]
work=base/'work';rows=[]
for case in ['baseline','changed-payload','missing-payload','hidden-extra','empty-directory','wrong-manifest-anchor','changed-report','restored']:
 if work.exists():shutil.rmtree(work)
 shutil.copytree(fixture,work)
 a=list(anchors)
 if case=='changed-payload':(work/'note.md').write_text('changed\n')
 if case=='missing-payload':(work/'note.md').unlink()
 if case=='hidden-extra':(work/'.extra').write_text('extra\n')
 if case=='empty-directory':(work/'extra').mkdir()
 if case=='wrong-manifest-anchor':a[1]='0'*64
 if case=='changed-report':(work/'REPORT.md').write_text('altered\n')
 before=ns['inventory'](work)
 result=subprocess.run([sys.executable,'-B',str(work/'verify.py'),str(work),*a],capture_output=True,text=True,timeout=10)
 after=ns['inventory'](work)
 assert before==after
 expected=case in ['baseline','restored'];assert (result.returncode==0)==expected,(case,result)
 rows.append({'case':case,'exit_code':result.returncode,'expected_accept':expected,'unchanged_by_verifier':before==after,'stdout':result.stdout,'stderr':result.stderr})
shutil.rmtree(work)
(base/'fixture-anchors.json').write_text(json.dumps(dict(zip(['FINAL.md','MANIFEST.json','REPORT.md'],anchors)),indent=2)+'\n')
(base/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'controls':len(rows),'all_expected':True,'all_read_only':True,'fixture_payload_files':3}))
