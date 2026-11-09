from pathlib import Path
import hashlib,json,re,stat
root=Path(__file__).resolve().parent; repo=root.parents[3]; packet=root/'packet'
def sha(b): return hashlib.sha256(b).hexdigest()
paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/NEW-TEN-2026-10-14.md','frontier/iterations/i13-fresh-discovery.md','frontier/iterations/i164-structural-graph-discovery.md','frontier/iterations/i198-geometry-representation-discovery.md']
paths += [str(p.relative_to(repo)) for p in (repo/'frontier/findings').glob('R*.md') if re.match(r'R(02[3-9]|03[0-9]|040)-',p.name)]
base='frontier/campaigns/2026-10-14/'
groups={
'fresh-structural-discovery-r21':['candidate.md','checkpoint.md'],
'fresh-structural-discovery-r23':['checkpoint.md'],
'fresh-structural-discovery-r25':['candidate.md','primary-comparison.md'],
'fresh-structural-discovery-r32':['screen-171.md','history-and-disposition.md'],
'fresh-structural-discovery-r35':['matching120.md'],
'fresh-structural-discovery-r75':['comparison.md','progress.md'],
'fresh-structural-discovery-r101':['working-threshold.md'],
'fresh-structural-discovery-r111':['packet/public/screen-120.md','packet/public/screen-168.md','packet/public/screen-175.md'],
'fresh-structural-discovery-r113':['packet/public/report.md'],
'fresh-structural-discovery-r114':['packet/public/screen-171-247.md','packet/public/screen-185.md'],
'fresh-structural-discovery-r116':['packet/public/'+x for x in ['report.md','screen-118.md','screens-157-186.md','history.md','reading.md']],
'fresh-structural-discovery-r117':['packet/public/'+x for x in ['report.md','structural-screens.md','online-fairness.md','automata.md','reading.md']],
'fresh-arithmetic-discovery-r80':['packet/public/research.md','packet/public/reading-limits.md'],
'fresh-analytic-discovery-r115':['packet/public/research-report.md'],
 't152ac116-contribution-r1':['review.md','reading-limits.md']}
for d,names in groups.items(): paths += [base+d+'/'+n for n in names]
rows=[]
for p in paths:
    path=repo/p
    if not path.exists(): raise RuntimeError('Missing context '+p)
    b=path.read_bytes(); rows.append({'path':p,'bytes':len(b),'sha256':sha(b),'reading_extent':'See public/reading.md; this identity is not a complete-reading claim.'})
(packet/'private/context-identities.json').write_text(json.dumps(rows,indent=2)+'\n')
files=[]; dirs=[]
for p in sorted(packet.rglob('*')):
    if p.is_symlink(): raise RuntimeError('symlink')
    if p.is_dir(): dirs.append(p.relative_to(packet).as_posix())
    else:
        if p.name=='MANIFEST.json': raise RuntimeError('already sealed')
        b=p.read_bytes(); files.append({'path':p.relative_to(packet).as_posix(),'bytes':len(b),'mode':stat.S_IMODE(p.stat().st_mode),'sha256':sha(b)})
reporthash=sha((packet/'public/report.md').read_bytes())
m={'schema':'r118-exact-packet-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','status':'prefreeze; no target; no nominee; no contribution/count/gate assignment','report':{'path':'public/report.md','sha256':reporthash},'directories':dirs,'files':files}
b=(json.dumps(m,indent=2)+'\n').encode()
with (packet/'MANIFEST.json').open('xb') as f: f.write(b)
anchors={'finalhash':sha(b),'reporthash':reporthash,'verifier_sha256':sha((packet/'public/verify.py').read_bytes()),'pin':m['pin'],'payload_files':len(files),'context_identities':len(rows),'status':m['status']}
(root/'FINAL-ANCHORS.json').write_text(json.dumps(anchors,indent=2)+'\n')
(root/'REPORT.md').write_text('# Round118 handoff\n\nPrefreeze archive; no target frozen, no nominee, and no author gate/count assignment.\n\nRead [public report](packet/public/report.md), [matrix reduction](packet/public/orthogonalization.md), [other screens](packet/public/screens.md), and [reading limits](packet/public/reading.md).\n\nDetached MANIFEST.json SHA256: `'+anchors['finalhash']+'`\n\nDetached public/report.md SHA256: `'+reporthash+'`\n\nThe read-only verifier requires both external anchors and the complete canonical tree. Copied controls are recorded in controls/results.json. No shared files were changed; no publication, upload, contact, nested agent or formal/manuscript workflow was used.\n')
print(json.dumps(anchors,indent=2))
