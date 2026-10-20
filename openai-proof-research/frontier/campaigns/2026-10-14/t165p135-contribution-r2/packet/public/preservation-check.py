#!/usr/bin/env python3
"""MIT. Read external originals, write evidence ONLY inside this review root."""
from pathlib import Path
import hashlib,json,stat
HERE=Path(__file__).resolve().parents[2]
PROJECT=HERE.parents[3]
def record(p):
 s=p.lstat();d={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,'type':'file' if p.is_file() else 'directory'}
 if p.is_file():d.update(size=s.st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 return d
start=json.loads((HERE/'work/start-inputs.json').read_text())
end={p:record(PROJECT/p) for p in start}
changes={p:{'before':start[p],'after':end[p]} for p in start if start[p]!=end[p]}
more=json.loads((HERE/'work/additional-inputs-start.json').read_text())
additional={p:hashlib.sha256((PROJECT/p).read_bytes()).hexdigest() for p in more}
assert all(additional[p]==e['sha256'] for p,e in more.items() if e.get('stability')!='mutable_navigation_only')
late=[]
for name in ['fresh-structural-discovery-r135','t165p135-contribution-r1','discovery-structural-r135-parent']:
 root=HERE.parent/name
 late.extend({'path':str(p.relative_to(PROJECT)),'metadata':record(p)} for p in root.rglob('*') if str(p.relative_to(PROJECT)) not in start)
assert not changes,changes
out={'stable_initial_entries':len(start),'initial_entries_unchanged':not changes,'additional_stable_files_unchanged':True,'mutable_navigation_changes':{p:{'before':e['sha256'],'after':additional[p]} for p,e in more.items() if e.get('stability')=='mutable_navigation_only' and additional[p]!=e['sha256']},'additional_end_sha256':additional,'late_additions_separate':late,'whole_author_and_prior_review_roots_unchanged':not any(x['path'].split('/')[3] in ['fresh-structural-discovery-r135','t165p135-contribution-r1'] for x in late),'changes':changes,'limits':'start snapshot follows initial AGENTS/role/disposition instruction reads; some history navigation precedes engagement binding as recorded; preservation observation, not syscall denial or historical-read certificate'}
(HERE/'work/preservation.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps(out,sort_keys=True))
