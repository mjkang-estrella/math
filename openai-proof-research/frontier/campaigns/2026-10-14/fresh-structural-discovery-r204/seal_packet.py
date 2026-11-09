from pathlib import Path
import os,shutil,json,hashlib,stat,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r204')
P=R/'packet';assert not P.exists(),'Main packet already exists; do not reseal'
assert not (R/'REPORT.md').exists(),'Outside report already exists; do not reseal'
# Privacy of our own working copies; no shared/upstream file is chmodded.
for d,ds,fs in os.walk(R/'private'):
 Path(d).chmod(0o700)
 for f in fs:(Path(d)/f).chmod(0o600)
selected=['FINAL.md','DERIVATIONS.md','guards.py','verify_packet.py','acquire.py','history_navigation.py','get_primary.py','copied_controls.py',
'private/READING.md','private/read-extents.json','private/artifact-controls.json','private/AGENTS.md','private/upstream.json','private/acceptance.bin','private/source328-catalogue.bin','private/selected-tree.json','private/authenticated.json','private/lean-328.md','private/lean-328-metadata.json','private/ReflexiveFixedPoints.lean','private/comparator-metadata.json','private/history-navigation.json','private/original-history-read.json','private/original-i88-section.md',
'private/primary/access.json','private/primary/mirror-access.json','private/primary/bruck1974.pdf','private/primary/bruck1974.txt','private/primary/bruck1974-p4.png','private/primary/wisnicki2012.pdf','private/primary/wisnicki2012.txt','private/primary/dominguez-lorenzo2001.pdf','private/primary/dominguez-lorenzo2001.txt','private/primary/dominguez-lorenzo2001-p3.png','private/primary/dominguez-lorenzo2001-p8.png','private/primary/dominguez-lorenzo-access.json','private/primary/bruck1973-web-access.json','private/primary/bruck1975-web-body.txt']
for x in json.loads((R/'private/authenticated.json').read_text())['blobs']:selected.append(x['local'])
assert len(selected)==len(set(selected))
P.mkdir(mode=0o755)
for rel in selected:
 src=R/rel; assert src.is_file() and not src.is_symlink(),rel
 dst=P/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);dst.chmod(0o400 if rel.startswith('private/') else 0o444)
 assert src.read_bytes()==dst.read_bytes()
dirs={'.':'0755'}
for d,ds,fs in os.walk(P):
 p=Path(d);rel=p.relative_to(P).as_posix();mode=0o700 if rel=='private' or rel.startswith('private/') else 0o755;p.chmod(mode);dirs[rel]=f'{mode:04o}'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[]
for rel in sorted(selected):
 p=P/rel;files.append({'path':rel,'bytes':p.stat().st_size,'mode':f'{stat.S_IMODE(p.stat().st_mode):04o}','sha256':sha(p)})
m={'format':'r204-exact-selection-v1','sealed_once_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'own selected r204 packet only; no inherited manifest','manifest_mode':'0444','directories':dict(sorted(dirs.items())),'files':files}
(P/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=2,ensure_ascii=False)+'\n');(P/'MANIFEST.json').chmod(0o444)
fhash=sha(P/'FINAL.md');mhash=sha(P/'MANIFEST.json')
report=f'''# Outside report — r204

PREFREEZE / no nominee. Full integrated derivations and unresolved obligations are in packet/DERIVATIONS.md. The unrestricted reflexive asymptotic extension and orbit-limit fixed-point-property step are unproved here. No mathematical grade, acceptance or count is assigned.

The exact selected packet has {len(files)} files plus its new MANIFEST, with {len(dirs)} directories. All twelve canonical blobs and both indicated Lean navigation/comparator bodies were authenticated; the comparator's theorem ends in sorry. Exact reading/version/access/history limits are retained privately. All work stayed local in the r204 root; no shared, git, peer, nested-agent or public actions were performed.

Main packet sealed once. This REPORT is outside it. Protected copies retain their original rights. Filesystem modes are explicit in the MANIFEST; private payload files are 0400 and private directories 0700. Mathematical source tree modes remain separately recorded as upstream metadata.

Detached FINAL SHA256: {fhash}
Detached MANIFEST SHA256: {mhash}

The REPORT SHA256 is detached in ANCHORS.json and the final handoff; it is intentionally not embedded here. The read-only verifier requires all three anchors explicitly and checks exact file/directory selection, sizes, modes and bytes. Five tiny copied controls use their own fresh toy selection: intact accepted; altered payload, altered mode, unlisted file and altered outside REPORT rejected. These are artifact checks, not mathematical gates.
'''
(R/'REPORT.md').write_text(report);(R/'REPORT.md').chmod(0o444);rhash=sha(R/'REPORT.md')
a={'FINAL_SHA256':fhash,'MANIFEST_SHA256':mhash,'REPORT_SHA256':rhash,'packet':str(P.resolve()),'outside_report':str((R/'REPORT.md').resolve()),'sealed_main_packet_count':1}
(R/'ANCHORS.json').write_text(json.dumps(a,indent=2)+'\n');(R/'ANCHORS.json').chmod(0o444)
print(json.dumps(a,indent=2));print('selected files',len(files),'directories',len(dirs))
