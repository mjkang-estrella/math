"""Recheck immutable provenance, read ranges, inputs, and deliverable hashes."""
from pathlib import Path
import hashlib, json, re

ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i10_complex_modes_r2'
REPORT=ROOT/'frontier/reviews/i10-complex-prime-modes-r2.md'
def sha(data): return hashlib.sha256(data).hexdigest()
def dump(name,obj): (OUT/name).write_text(json.dumps(obj,indent=2)+'\n')
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
assert not tree['truncated']
blobs={e['path']:e['sha'] for e in tree['tree'] if e['type']=='blob'}
dirs=sorted(e['path'] for e in tree['tree'] if e['type']=='tree' and e['path'].count('/')==1)
screen=re.compile('prime|primitive|multiplicative|dirichlet|riemann|elliott|chowla|dickman|sieve|totient|factor',re.I)
dump('inventory-screen.json',dict(tree_entries=len(tree['tree']),manuscript_directories=len(dirs),
    truncated=False,tree_sha256=sha((ROOT/'sources/preprints-tree.json').read_bytes()),
    screen_regex=screen.pattern,all_directories=dirs,selected_directories=[p for p in dirs if screen.search(p)]))

verified=[]
for manifest in ['frontier/sources/i07_arithmetic/retrieval-manifest.json',
                 'frontier/sources/i10_complex_modes/retrieval-manifest.json',
                 'frontier/sources/i10_complex_modes_r2/retrieval-manifest.json']:
    records=json.loads((ROOT/manifest).read_text())['files']
    for row in records:
        data=(ROOT/row['local']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob==blobs[row['path']] and sha(data)==row['sha256']
    verified.append(dict(manifest=manifest,files=len(records),passed=True))

# Inclusive ranges actually inspected for this audit; a source theorem is a premise.
ranges={
 'The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/02-preliminaries.tex':[(236,271)],
 'The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/03-determinant.tex':[(1,115)],
 'The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/05-major-arcs.tex':[(44,163)],
 'The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/06-correlations.tex':[(1,935)],
 'The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/07-extraction.tex':[(1,702)],
 'The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/08-poisson-dirichlet.tex':[(1,266)],
 'The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/09-long-prime-appendix.tex':[(1,155),(238,658)],
 'Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/08-type-ii.tex':[(90,252)],
 'Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/sections/02-transference.tex':[(1190,1340)],
 'Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/sections/03-ideal-kernels.tex':[(1,58),(270,300),(414,450)],
 'The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex':[(90,145)],
 'Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/introduction.tex':[(1,100)],
 'Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/sections/03-shifted.tex':[(52,92),(507,552)],
}
range_records=[]
for short,spans in ranges.items():
    path=OUT/'pinned/preprints'/short
    lines=path.read_bytes().splitlines(keepends=True)
    for start,end in spans:
        end=min(end,len(lines))
        data=b''.join(lines[start-1:end])
        range_records.append(dict(path=str(path.relative_to(ROOT)),start_line=start,end_line=end,
            sha256=sha(data),labels=re.findall(r'\\label\{([^}]+)\}',data.decode())))
dump('source-ranges.json',range_records)

changed=[]
for row in json.loads((OUT/'input-manifest.json').read_text()):
    if sha((ROOT/row['path']).read_bytes())!=row['sha256']: changed.append(row['path'])
assert not changed, changed
assert len(REPORT.read_text())>1000
validation=dict(pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
    verified_manifests=verified,changed_inputs=changed,
    candidate_lines=len((ROOT/'frontier/iterations/i10-complex-prime-modes.md').read_text().splitlines()),
    candidate_sha256=sha((ROOT/'frontier/iterations/i10-complex-prime-modes.md').read_bytes()),
    report_sha256=sha(REPORT.read_bytes()),
    diagnostics=json.loads((ROOT/'frontier/experiments/i10_complex_modes_r2/results.json').read_text()),
    limitations='Hashes and finite identities do not prove asymptotic estimates or worldwide novelty.')
dump('final-validation.json',validation)
artifacts=[REPORT]
for directory in [OUT,ROOT/'frontier/experiments/i10_complex_modes_r2']:
    artifacts += [p for p in directory.rglob('*') if p.is_file() and p.name!='artifact-manifest.json']
dump('artifact-manifest.json',[dict(path=str(p.relative_to(ROOT)),bytes=len(p.read_bytes()),
    sha256=sha(p.read_bytes())) for p in sorted(artifacts)])
print(json.dumps(dict(verified_manifests=verified,changed_inputs=changed,
    report_sha256=validation['report_sha256'],artifacts=len(artifacts)),indent=2))
