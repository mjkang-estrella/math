"""One-time own-packet seal. Refuses any existing final seal outputs."""
from pathlib import Path
import hashlib,json,os,stat
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r205')
os.umask(0o077)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
outside=['MANIFEST.json','REPORT.md','ANCHORS.json','verification.json']
for f in outside:
 if (ROOT/f).exists():raise RuntimeError('Refusing reseal/overwrite: '+f)
entries=[];directories={'.':'0700'};ROOT.chmod(0o700)
for p in sorted(ROOT.rglob('*')):
 rel=p.relative_to(ROOT).as_posix()
 if rel=='controls' or rel.startswith('controls/'):continue
 if p.is_symlink():raise RuntimeError('Unexpected own-root symlink')
 if p.is_dir():p.chmod(0o700);directories[rel]='0700';continue
 if rel in outside:continue
 mode=0o400 if rel.startswith('private/') else 0o444;p.chmod(mode)
 entries.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p),'mode':format(mode,'04o'),'rights':'private original-rights retained body or local evidence' if rel.startswith('private/') else 'original r205 author notes/code; unpublished'})
manifest={'schema':'r205-exact-selection-v1','description':'Own exact r205 selection, sealed once. No inherited manifest. Protected source/primary/history/metadata local under original rights.','files':entries,'directories':directories,'outside_files':outside,'outside_directories':['controls']}
with (ROOT/'MANIFEST.json').open('x') as f:json.dump(manifest,f,indent=2);f.write('\n')
(ROOT/'MANIFEST.json').chmod(0o444)
fh=sha(ROOT/'FINAL.md');mh=sha(ROOT/'MANIFEST.json')
controls=json.loads((ROOT/'controls/results.json').read_text())
assert controls['baseline']['artifact_checks']=='passed' and all(x['rejected'] for x in controls['negative_controls'].values())
report=f'''# Outside report — r205 Source329

Disposition: PREFREEZE / no nominee. No theorem was frozen for nomination and no correctness, contribution, acceptance, or count was assigned.

The author completed and retained the strongest source/classical construction, including the exact bound n <= exp(C_a b^(2h) log(2+b)), h=ceil(3^(1000a)); kernel-sum and common-kernel saturation proofs; and the fully integrated higher-contraction route with the same ambient-dimension exponent. The remaining research obligation is a nonroutine operation beyond that composition, such as a smaller T-indicator description with every simultaneous separation and uniform signed-approximation constraint proved. No such result is claimed.

All eleven canonical blobs were authenticated. All operative TeX and includes were read; the PDF was authenticated only. The pinned indicated Lean comparator ends in sorry. Primary and actual eligible original sections were read under the detailed recorded limits. No history clearance or worldwide-priority assertion. Root-owned derivations and private original-rights bodies remain separate.

Selected files: {len(entries)}; selected bytes: {sum(x['bytes'] for x in entries)}. This REPORT is outside the manifest selection. MANIFEST excludes itself and the detached anchor/verification records. controls/ contains fresh tiny copied-author-file manifests, never a reduced inherited manifest.

Detached FINAL SHA256: {fh}
Detached MANIFEST SHA256: {mh}
The outside REPORT's own SHA256 is detached in ANCHORS.json and the final handoff.

Copied controls: baseline passed; altered content, altered file mode, and an extra selected-tree file were rejected; original author files were unchanged. These are artifact checks only. A subsequent read-only verification must receive all three hashes as explicit arguments; no self-read hash default is provided. Its receipt is outside the selection as verification.json.

Authorized provenance: Codex / GPT-6 Astra / xhigh / default service tier. No nested agents, git/shared edits, browser UI, public actions, formalization, manuscript, or release. Parent alone integrates, reviews, adopts grades, and counts.
'''
with (ROOT/'REPORT.md').open('x') as f:f.write(report)
(ROOT/'REPORT.md').chmod(0o444)
anchors={'FINAL.md':fh,'MANIFEST.json':mh,'REPORT.md':sha(ROOT/'REPORT.md')}
with (ROOT/'ANCHORS.json').open('x') as f:json.dump(anchors,f,indent=2);f.write('\n')
(ROOT/'ANCHORS.json').chmod(0o444)
print(json.dumps(anchors,indent=2));print('Sealed own exact selection once:',len(entries),'files.')
