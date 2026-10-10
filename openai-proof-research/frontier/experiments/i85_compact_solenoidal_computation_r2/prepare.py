"""Preparation only. Writes exclusively I85-owned metadata; never used by verifier."""
from pathlib import Path
import json,hashlib,shutil,difflib
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i85_compact_solenoidal_computation_r2'
E=R/'frontier/experiments/i85_compact_solenoidal_computation_r2'
A=R/'frontier/sources/i80_geometric_flows_computation_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,o):p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
def ref(p):
 p=Path(p); b=(R/p).read_bytes();return dict(path=str(p),sha256=sha(b),bytes=len(b))
mutable=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
inputs=[]
for p in mutable+['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/iteration85-compact-solenoidal-computation-r2-task.json']:
 dst=S/'snapshots'/p;dst.parent.mkdir(parents=True,exist_ok=True)
 if not dst.exists():shutil.copyfile(R/p,dst)
 inputs.append(dict(ref(dst.relative_to(R)),live_path=p,mutable=p in mutable))
dump(S/'inputs.json',inputs)
task=json.loads((R/'frontier/iterations/iteration85-compact-solenoidal-computation-r2-task.json').read_text())
(S/'full-brief.txt').write_text(task['brief'])
refs=[]
for p in [*A.rglob('*'),R/'frontier/iterations/i80-geometric-flows-computation-discovery.md',R/'frontier/experiments/i80-parent-verification.json',R/'frontier/experiments/i80_geometric_flows_computation_discovery/verify.py',R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json',R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl',R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/seal-v1.json']:
 if p.is_file():refs.append(ref(p.relative_to(R)))
dump(S/'immutable-references.json',sorted(refs,key=lambda a:a['path']))
m=json.loads((A/'source-manifest.json').read_text());families={'RV','ES','VD','SP','IB','GS','FS','PI','FP'}
m=[x for x in m if x['family'] in families];dump(S/'source-manifest.json',m)
reads=[json.loads(l) for l in (S/'reading-deliveries.jsonl').read_text().splitlines()]
# These were read in full before the logging reader was introduced.
for suffix in ['build/main.tex','build/addressed.tex']:
 a=next(x for x in m if x['family']=='RV' and x['path'].endswith(suffix));b=(R/a['path']).read_bytes();reads.append(dict(a,start=1,end=len(b.splitlines()),total_lines=len(b.splitlines()),passage_sha256=sha(b),delivery='earlier complete direct tool reading'))
a=ref('frontier/iterations/i80-geometric-flows-computation-discovery.md');b=(R/a['path']).read_bytes();reads.append(dict(a,start=1,end=len(b.splitlines()),passage_sha256=sha(b),delivery='complete actual report in three displayed ranges; also supplied in brief'))
for x in reads:x['coverage_kind']='semantic_passage_read'
dump(S/'passages.json',reads)
# Version equality is recorded distinctly from semantic reading.
versions=[]
for a in m:
 if a['family']=='IB' and 'October-6-2026/build/' in a['path']:
  old=a['path'].replace('October-6-2026','September-27-2026');b=next((x for x in m if x['path']==old),None)
  if b:
   versions.append(dict(old=b['path'],new=a['path'],old_sha256=b['sha256'],new_sha256=a['sha256'],identical=(R/old).read_bytes()==(R/a['path']).read_bytes()))
dump(S/'ib-versions.json',versions)
coverage=[]
for x in m:
 if not x['path'].endswith('.tex'):continue
 n=len((R/x['path']).read_bytes().splitlines());covered=set()
 for p in reads:
  if p['path']==x['path']:covered.update(range(p['start'],p['end']+1))
 # Do not turn identical-version bindings into semantic read claims.
 gaps=[];begin=None
 for i in range(1,n+2):
  if i<=n and i not in covered:
   if begin is None:begin=i
  elif begin is not None:gaps.append([begin,i-1]);begin=None
 coverage.append(dict(path=x['path'],family=x['family'],lines=n,read_lines=len(covered),unread_ranges=gaps))
dump(S/'read-coverage.json',dict(scope='C80 proof dependencies and fluid contracts; not exhaustive contribution clearance',files=coverage,version_identity_is_not_reading=True,unread='Unused IB/PI symbolic and routing variants, duplicate-version files, bibliographies and unrelated geometric manuscripts are not silently credited.'))
primary=[json.loads(l) for l in (S/'primary-readings.jsonl').read_text().splitlines()]
p=A/'primary/okabe-brandolese.txt';b=p.read_bytes();primary.append(dict(ref(p.relative_to(R)),start=160,end=210,passage_sha256=sha(b''.join(b.splitlines(keepends=True)[159:210]))))
dump(S/'primary-passages.json',primary)
events=json.loads((S/'preseal-events.json').read_text())
for message in [
 'System Python, /usr/bin/python3, /tmp/agvenv and /tmp/cvenv lacked sympy. First diagnostic run failed ModuleNotFoundError before assertions. System Python lacked pip. Downloaded exact sympy 1.14.0 and mpmath 1.3.0 wheels through existing /tmp/agvenv pip into owned runtime only; imported zipped wheels. No original mathematical formula changed.',
 'Combined PI sheet/compact/autonomous read delivery truncated the compact-reciprocal portion; compact-reciprocal was reread completely. Prefix-realizations 341-676 delivery truncated around 530-560; 510-585 was reread. Full primary batch truncated around DGMP/Gavrilov/CLV; affected ranges were reread separately. These duplicate bindings reflect actual completed coverage, not credit from truncation.',
 'Two guessed primary extraction filenames did not exist; corrected after directory inventory. No network source theorem is used as a proof premise.',
 'Broad ledger search and task JSON printing exceeded output budgets. Only scoped visible ledger status is claimed read. Complete task brief was already provided in conversation and is retained exactly by extraction; full file hash is not a new semantic-reading claim.'
]:
 if not any(x['event']==message for x in events):events.append(dict(event=message))
dump(S/'preseal-events.json',events)
# Context, not a mathematical claim of novelty.
dump(S/'scope.json',dict(proof='ORIGINAL PASS WITHOUT REPAIRS',nomination='HELD',accepted_count_increment=0,accepted_count=8,contribution='NOT REVIEWED; separate independent round required',broad_i80_assignment='NOT FULLY DISCHARGED',geometry_G_R='NOT NOMINATED; no scoped proof verdict',finite_completion='UNUSED BY C80',infinite_completion='OPEN; UNUSED BY C80',external_constructions_as_premises=False))
print(json.dumps(dict(references=len(refs),source_files=len(m),passages=len(reads),version_comparisons=len(versions))))
