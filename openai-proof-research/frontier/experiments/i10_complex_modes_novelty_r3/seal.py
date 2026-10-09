"""Seal this review's evidence and verify inherited identity records; no shared writes."""
import hashlib, json, pathlib, re
from evidence import ROOT, OUT, PIN, sha, stamp, write

REPORT = ROOT/'frontier/reviews/i10-complex-modes-novelty-r3.md'
EXP = ROOT/'frontier/experiments/i10_complex_modes_novelty_r3'
def record(p):
 b=p.read_bytes()
 return dict(path=str(p.relative_to(ROOT)), bytes=len(b), sha256=sha(b))
def readjson(p): return json.loads(p.read_text())
def rows(v): return v if isinstance(v,list) else v['files']
def check_records(rs):
 errors=[]
 for r in rs:
  p=ROOT/r.get('local',r.get('path'))
  if not p.exists() or sha(p.read_bytes())!=r['sha256']: errors.append(str(p.relative_to(ROOT)))
 return errors

tree=readjson(ROOT/'sources/preprints-tree.json')
lookup={r['path']:r for r in tree['tree']}
assert tree['truncated'] is False
errors=[]; counts={}; deps=set()
for group in ['i07_arithmetic','i10_complex_modes','i10_complex_modes_r2']:
 p=ROOT/'frontier/sources'/group/'retrieval-manifest.json'; deps.add(p)
 rs=rows(readjson(p)); counts[group]=len(rs)
 for r in rs:
  f=ROOT/r['local']; b=f.read_bytes(); deps.add(f)
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  if sha(b)!=r['sha256'] or blob!=r['git_blob'] or blob!=lookup[r['path']]['sha']: errors.append(str(f))
for name in ['input-manifest.json','artifact-manifest.json']:
 p=ROOT/'frontier/sources/i10_complex_modes_r2'/name; deps.add(p)
 rs=rows(readjson(p)); counts['r2_'+name]=len(rs); errors+=check_records(rs)
 for r in rs: deps.add(ROOT/r.get('local',r.get('path')))

initial=rows(readjson(OUT/'input-manifest.json'))
errors+=check_records(initial); counts['own_initial_inputs']=len(initial)
for r in initial: deps.add(ROOT/r['path'])
fresh=readjson(OUT/'retrieval-manifest.json'); counts['fresh_pinned']=len(fresh)
for r in fresh:
 p=ROOT/r['local']; b=p.read_bytes()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if sha(b)!=r['sha256'] or blob!=lookup[r['path']]['sha']: errors.append(str(p))

literature=[]
for name in ['literature-manifest.json','literature-additional.json']:
 for r in readjson(OUT/name):
  if r.get('local'):
   p=ROOT/r['local']; t=p.with_suffix('.txt'); literature.append(r)
   if sha(p.read_bytes())!=r['sha256'] or sha(t.read_bytes())!=r['text_sha256']: errors.append(str(p))
counts['successful_literature_PDFs']=len(literature)

ranges=readjson(OUT/'inspected-ranges.json')
# These complete readings occurred earlier in the same review, before or apart
# from the helper. This records the attestation without inventing read timestamps.
full=[
 'frontier/iterations/i10-complex-prime-modes.md',
 'frontier/reviews/i10-complex-prime-modes-r2.md',
 'frontier/iterations/i10-complex-modes-proof-integration.md',
 'frontier/iterations/i07-arithmetic.md',
 'frontier/findings/R006-progression-PD-primitive-root-density.md',
 'frontier/findings/R008-parity-PD-independence.md',
 'frontier/reviews/i03-arithmetic-progressions-r4.md',
 'frontier/reviews/i03-arithmetic-novelty-r5.md',
 'frontier/reviews/i05-parity-pd-r2.md',
 'frontier/reviews/i05-parity-novelty-r3.md',
 'AGENTS.md', 'sources/upstream.json']
for path in full:
 b=(ROOT/path).read_bytes()
 ranges.append(dict(path=path,start=1,end=len(b.decode().splitlines()),sha256=sha(b),
   record_kind='retrospective complete-read attestation, same session',recorded_utc=stamp()))
for r in ranges:
 p=ROOT/r['path']; b=p.read_bytes(); lines=b.decode().splitlines(); deps.add(p)
 if sha(b)!=r['sha256']: errors.append(r['path'])
 r['range_sha256']=sha(('\n'.join(lines[r['start']-1:r['end']])+'\n').encode())
write('range-seals.json',dict(numbering='Python str.splitlines, one-based inclusive',ranges=ranges,
 visual_pages=[dict(pdf='literature/timofeev-1992-final.pdf',pdf_page=3,printed_page=1191,image='literature/timofeev-character-asymptotic.png'),dict(pdf='literature/timofeev-1992-final.pdf',pdf_page=4,printed_page=1192,image='literature/timofeev-theorems.png')]))

# Include the skill instructions used for PDF interpretation without copying them.
skill=pathlib.Path('/home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1007.11041/skills/pdf/SKILL.md')
write('dependency-seal.json',dict(pin=PIN,sealed_utc=stamp(),files=[record(p) for p in sorted(deps)],
 external_instruction=dict(path=str(skill),sha256=sha(skill.read_bytes()))))

broken=[]
for target in re.findall(r'\]\(([^\n)]+)\)',REPORT.read_text()):
 if target.startswith(('http:','https:','#')): continue
 p=(REPORT.parent/target.split('#')[0]).resolve()
 if not p.exists() and p.name not in ['artifact-seal.json','validation.json']: broken.append(target)

artifacts=sorted([p for base in [OUT,EXP] for p in base.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['artifact-seal.json','validation.json']]+[REPORT])
write('artifact-seal.json',dict(sealed_utc=stamp(),exclusions=['artifact-seal.json','validation.json','__pycache__'],files=[record(p) for p in artifacts]))
write('validation.json',dict(validated_utc=stamp(),pin=PIN,counts=counts,
 complete_tree=dict(entries=len(tree['tree']),blobs=sum(r['type']=='blob' for r in tree['tree']),directories=len({r['path'].split('/')[1] for r in tree['tree']}),truncated=tree['truncated']),
 identity_errors=errors,broken_report_links=broken,artifact_records=len(artifacts),
 own_initial_inputs_unchanged=not check_records(initial),exact_reduction_checks=readjson(OUT/'reduction-checks.json')['all_assertions_passed'],
 verdict='ACCEPT as one substantial qualified deduction; existing proof PASS preserved; count unchanged',
 all_checks_passed=not errors and not broken))
print(json.dumps(readjson(OUT/'validation.json'),indent=2))
assert not errors and not broken
