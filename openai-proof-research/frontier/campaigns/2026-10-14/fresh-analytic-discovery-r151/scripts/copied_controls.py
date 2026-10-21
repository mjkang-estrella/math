from pathlib import Path
import hashlib,json,subprocess,sys,os
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r151');c=r/'private/controls';c.mkdir(exist_ok=True)
selection={'note.md':'DERIVATION.md','source.tex':'private/pinned/02-reductions.tex'}
for dest,src in selection.items():(c/dest).write_bytes((r/src).read_bytes())
(c/'FINAL.md').write_text('Selected two-file artifact control only; not a complete source or research packet.\n')
(c/'REPORT.md').write_text(json.dumps({'selection_relative_to_r151':selection,'rights':'Original rights retained; no inherited original manifest.'},indent=2)+'\n')
rows=[{'path':dest,'size':(c/dest).stat().st_size,'sha256':hashlib.sha256((c/dest).read_bytes()).hexdigest()} for dest in sorted(selection)]
(c/'MANIFEST.json').write_text(json.dumps({'schema':'r151-exact-files-v1','files':rows},indent=2)+'\n')
def sha(p):return subprocess.check_output(['sha256sum',str(p)],text=True).split()[0]
a={n:sha(c/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def state():
 return {str(p.relative_to(c)):(p.stat().st_mode,p.stat().st_size,p.stat().st_mtime_ns,sha(p)) for p in c.rglob('*') if p.is_file()}
def run(label,want,anchors=None):
 anchors=anchors or a;before=state();cmd=[sys.executable,'-B',str(r/'scripts/verify.py'),str(c),'--manifest-sha256',anchors['MANIFEST.json'],'--final-sha256',anchors['FINAL.md'],'--report-sha256',anchors['REPORT.md']];p=subprocess.run(cmd,capture_output=True,text=True,check=False);after=state();assert (p.returncode==0)==want and before==after,(label,p.stdout,p.stderr);return {'case':label,'expected_pass':want,'returncode':p.returncode,'read_only_observed':before==after,'output':json.loads(p.stdout)}
log=[run('baseline',True)];b=(c/'note.md').read_bytes();(c/'note.md').write_bytes(b+b'changed\n');log.append(run('changed payload',False));(c/'note.md').write_bytes(b)
s=(c/'source.tex').read_bytes();(c/'source.tex').unlink();log.append(run('missing payload',False));(c/'source.tex').write_bytes(s)
(c/'.extra').write_text('extra');log.append(run('hidden extra',False));(c/'.extra').unlink()
bad=dict(a);bad['MANIFEST.json']='0'*64;log.append(run('wrong detached anchor',False,bad));log.append(run('restored baseline',True))
for dest,src in selection.items():assert (c/dest).read_bytes()==(r/src).read_bytes()
(r/'private/control-results.json').write_text(json.dumps({'selection':selection,'fixture_anchors':a,'cases':log,'unchanged_selected_originals':True,'scope':'artifact properties only'},indent=2)+'\n')
print('Six copied controls matched expectations; verifier preserved every tested state; restored selection matches originals.')
