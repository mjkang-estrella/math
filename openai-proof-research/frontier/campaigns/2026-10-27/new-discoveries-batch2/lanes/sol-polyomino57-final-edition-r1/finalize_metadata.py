from pathlib import Path
import json,hashlib,zipfile,difflib
L=Path('source');old=zipfile.ZipFile('frozen-input.zip')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def w(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
p=L/'paper.txt';t=p.read_text().replace('The frozen input archive SHA-256 is:','The original manuscript input archive SHA-256 is:').replace('The PDF skill marker initially failed',"The original manuscript's PDF skill marker initially failed");p.write_text(t)
# Literal comparison of every mathematical paragraph/display; only these status paragraphs may differ.
a=old.read('paper.txt').decode().split('\n\n');b=t.split('\n\n');assert len(a)==len(b)
changed=[i for i,(x,y) in enumerate(zip(a,b)) if x!=y]
assert changed==[0,27,34,35,39,40,41],changed
assert a[0].splitlines()[:2]==b[0].splitlines()[:2]
for i in changed:print('STATUS-ONLY paragraph',i,a[i][:90])
# All explicitly indented mathematical display lines are byte-identical.
def displays(s):return [x for x in s.splitlines() if x.startswith('    ')]
assert displays('\n\n'.join(a))==displays(t)
for n in old.namelist():
 if n.startswith(('formal/','inherited/','evidence/','replay-evidence/')) or n in ['FAILURE-NOTES.md','source-manifest.json','consumed-modules.json','container.svg','pins.json']:
  assert (L/n).read_bytes()==old.read(n),n
sources=json.loads((L/'source-manifest.json').read_text());assert len(sources)==2023
for n,v in sources.items():assert sha(L/n)==v['sha256'] and (L/n).read_bytes()==old.read(n)
inv=json.loads((L/'replay-evidence/declaration-inventory.json').read_text());assert len(inv)==5924
for n in ['root-polyomino57-final-review-freeze-r1/root-fresh-replay/declaration-inventory.json','sol-polyomino57-full-final-review-r1/fresh-replay/declaration-inventory.json']:
 assert (L/'evidence'/n).read_bytes()==(L/'replay-evidence/declaration-inventory.json').read_bytes()
w(Path('CONTENT-IDENTITY.json'),dict(status='PASS',formal_sources=2023,actual_records=5924,all_source_bytes_unchanged=True,all_actual_records_byte_identical=True,inventory_sha256=sha(L/'replay-evidence/declaration-inventory.json'),all_indented_displays_exact=True,unchanged_manuscript_paragraphs=len(a)-len(changed),changed_status_only_paragraph_indices=changed,authorship_unchanged=True,original_evidence_and_dissent_and_failure_notes_unchanged=True,new_full_Lean_replay=False))
