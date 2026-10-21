#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,shutil,stat,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r122')
F=R/'private/copied-control';F.mkdir()
(F/'payload').mkdir()
SHA=lambda b:hashlib.sha256(b).hexdigest()
pairs=[(R/'packet/notes/integrated-metric-reduction.md',F/'payload/math.md'),(R/'private/pinned/preprints/Bounded-anticanonical-metrics-on-klt-pairs-and-torus-quotients-September-26-2026/build/source/sections/introduction.tex',F/'payload/source.tex')]
originals=[]
for src,dst in pairs:
    b=src.read_bytes();dst.write_bytes(b);originals.append({'source':str(src.relative_to(R)),'selected_copy':str(dst.relative_to(F)),'size':len(b),'sha256':SHA(b)})
(F/'FINAL.md').write_text('Reduced copied artifact fixture only. No mathematical verdict.\n')
(F/'REPORT.md').write_text('Two selected payloads with own exact membership. No inherited source/root manifest.\n')
manifest={'schema':1,'label':'r122 reduced selected-copy controls','payload':[{'path':str(dst.relative_to(F)),'size':dst.stat().st_size,'sha256':SHA(dst.read_bytes())} for _,dst in pairs],'directories':['payload']}
(F/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
anchors={n:SHA((F/n).read_bytes()) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snap(root):
    out={}
    for base,dirs,files in os.walk(root,followlinks=False):
        for n in dirs+files:
            p=Path(base)/n;s=p.lstat();out[str(p.relative_to(root))]={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,'kind':'dir' if p.is_dir() else 'file','hash':SHA(p.read_bytes()) if p.is_file() else None}
    return out
results=[]
def run(name,want,aa=None):
    a=aa or anchors;before=snap(F)
    cmd=[sys.executable,'-B',str(R/'tools/verify.py'),str(F),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']]
    v=subprocess.run(cmd,capture_output=True,text=True,check=False)
    after=snap(F);ok=(v.returncode==0)==want and before==after
    results.append({'case':name,'expected_accept':want,'exit_code':v.returncode,'verifier_output':json.loads(v.stdout),'read_only_snapshot_unchanged':before==after,'expected_behavior':ok})
    if not ok:raise RuntimeError(name)
run('baseline',True)
p=F/'payload/math.md';b=p.read_bytes();p.write_bytes(b+b'\nmodified\n');run('modified-payload',False);p.write_bytes(b)
p.unlink();run('missing-payload',False);p.write_bytes(b)
(F/'.hidden-extra').write_text('extra\n');run('hidden-extra',False);(F/'.hidden-extra').unlink()
(F/'empty-extra').mkdir();run('empty-extra-directory',False);(F/'empty-extra').rmdir()
wrong=dict(anchors);wrong['MANIFEST.json']='0'*64;run('wrong-detached-manifest',False,wrong)
run('restored',True)
for src,_ in pairs:
    expected=next(x for x in originals if x['source']==str(src.relative_to(R)))
    assert SHA(src.read_bytes())==expected['sha256']
(R/'private/copied-control-results.json').write_text(json.dumps({'fixture':str(F.relative_to(R)),'selected_originals':originals,'detached_fixture_anchors':anchors,'cases':results,'originals_unchanged':True,'snapshot_scope':'all descendants: bytes, type, modes and link counts; root directory mode omitted','mathematical_gate':False},indent=2)+'\n')
print(json.dumps({'cases':len(results),'expected_behavior':all(x['expected_behavior'] for x in results),'originals_unchanged':True,'mathematical_gate':False}))
