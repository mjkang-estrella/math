"""Create this task's exact selected packet once; source originals remain unchanged."""
from pathlib import Path
import importlib.util,shutil,json,hashlib,os,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r210')
P=R/'packet';M=R/'MANIFEST.json'
assert not P.exists() and not M.exists(), 'Already selected/sealed; do not reseal'
spec=importlib.util.spec_from_file_location('v',R/'verify_packet.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
expected=(R/'FROZEN-STATEMENT.sha256').read_text().split()[0]
assert v.sha(R/'FROZEN-STATEMENT.md')==expected
originals={}
def copy(src,dst):
 assert src.is_file() and not src.is_symlink()
 originals[str(src)]=v.sha(src);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
for name in ['FROZEN-STATEMENT.md','FROZEN-STATEMENT.sha256','AUTHOR-PROOF.md','READ-LIMITS.md','AUTHOR-CHECK.md','FINAL.md']:
 copy(R/name,P/name)
copy(R/'derivations/00-feasibility.md',P/'derivations/00-feasibility.md')
copy(R/'verify_packet.py',P/'artifact/verify_packet.py')
copy(R/'tiny_controls.py',P/'artifact/tiny_controls.py')
# This traversal is restricted to this task's own private files for exact selection.
for src in sorted((R/'private').rglob('*')):
 if src.is_file():copy(src,P/'private'/src.relative_to(R/'private'))
for name in ['guards.py','acquire.py','get_primary.py','history_pass.py']:
 copy(R/name,P/'private/invocation-scripts'/name)
# Private copies retain local restrictions; this does not change originals' rights or modes.
for root,dirs,files in os.walk(P):
 q=Path(root);private=q==P/'private' or (P/'private') in q.parents
 os.chmod(q,0o700 if private else 0o755)
 for name in files:os.chmod(q/name,0o600 if private else 0o644)
entries=[]
for path,data in sorted(v.inspect(P).items()):
 rights='protected-private-local-original-rights' if path=='private' or path.startswith('private/') else 'original-author-work-local-unpublished'
 entries.append(dict(path=path,rights=rights,**data))
manifest={'format':'r210-exact-selected-packet-v1','selection':'This task\'s own entire packet directory, exactly the entries below; no inherited manifest','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','final':'FINAL.md','frozen_statement_sha256':expected,'sealed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'entries':entries}
M.write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n');os.chmod(M,0o644)
fh=v.sha(P/'FINAL.md');mh=v.sha(M)
report=R/'REPORT.md'
report.write_text('''# r210 outside handoff report

Author-proof nominee: exact classification of smooth local R3 nonimmersion loci on (-1,1)^2 as relatively closed nowhere-dense sets, with uniform positive metric bounds, flat curvature jets on the prescribed set, regular curvature zeros off it, and a Euclidean full metric jet at 0 when prescribed bad. Exact hypotheses and quantifiers remain in packet/FROZEN-STATEMENT.md; the full author proof is packet/AUTHOR-PROOF.md.

The added operation is quantitative finite capture for bounded smooth immersion classes, with interior curvature mass separated from the boundary slope. This removes internal boundary accumulations and enables smooth local realization at every complementary point. Ordinary insertion, source cap/pulse estimates, curvature prescription and diagonal derivative summation remain paid.

No unproved bridge is substituted for any step of the frozen author proof. Independent adversarial correctness and substantial-contribution reviews remain pending; no grade, acceptance, count, manuscript or release is assigned. The earlier finite-regularity exploration is preserved as unproved and unused.

Read limits: all 12 Source334 blobs authenticated, all operative TeX read; three exact eligible original r22 sections only; all inherited exclusions remain installed. Actual primary proof operations read with explicit version limits. The 1989 Nakamura–Maeda publisher endpoint returned 403; the actual 1986 research report supplied the read existence interface. The pinned Lean comparator ends in sorry and supplies no completed endpoint proof. See packet/READ-LIMITS.md for exact extents, recovery, search false admissions and other access failures.

The packet was selected and sealed once using its own exact manifest. Protected source/primary/history/search material and named metadata are under packet/private with private file modes and their original rights. The original working files were not altered by copying. Tiny copied artifact controls accepted intact/restored copies and rejected changed bytes, extra files, mode changes and missing files. These are artifact checks, not mathematical gates. The provided verifier is read-only and requires explicit detached FINAL, MANIFEST and outside REPORT anchors; verification output is recorded separately after this report is hashed.

Detached FINAL SHA256: '''+fh+'''
Detached MANIFEST SHA256: '''+mh+'''
The outside REPORT's detached hash is in REPORT.sha256 and is supplied explicitly to the verifier. This file does not contain its own hash.
''')
os.chmod(report,0o644);rh=v.sha(report)
for name,hashvalue,target in [('FINAL',fh,'packet/FINAL.md'),('MANIFEST',mh,'MANIFEST.json'),('REPORT',rh,'REPORT.md')]:
 (R/(name+'.sha256')).write_text(hashvalue+'  '+target+'\n')
for name,old in originals.items():assert v.sha(Path(name))==old,'Copy changed original: '+name
print(json.dumps({'FINAL':fh,'MANIFEST':mh,'REPORT':rh,'files':sum(x['type']=='file' for x in entries),'directories':sum(x['type']=='directory' for x in entries),'selected_bytes':sum(x.get('bytes',0) for x in entries),'original_files_unchanged':len(originals)},indent=2))
