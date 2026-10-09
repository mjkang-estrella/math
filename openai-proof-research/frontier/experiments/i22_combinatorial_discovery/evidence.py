"""Build exact source/primary contracts and evidence metadata for I22."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[3]
S = ROOT/'frontier/sources/i22_combinatorial_discovery'

def digest(b): return hashlib.sha256(b).hexdigest()
def dump(name, data): (S/name).write_text(json.dumps(data,indent=2)+'\n')

def slice_record(path, first, last, purpose):
    lines=(ROOT/path).read_text().splitlines(keepends=True)
    text=''.join(lines[first-1:last])
    return {'path':path,'first_line':first,'last_line':min(last,len(lines)),
            'purpose':purpose,'text':text,'sha256':digest(text.encode())}

if __name__=='__main__':
    manifest=json.loads((S/'pinned-manifest.json').read_text())
    contracts=[]
    regex=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[[^\]]*\])?[\s\S]*?\\end\{\1\}')
    for row in manifest:
        path=S/'pinned'/row['path']
        t=path.read_text()
        for match in regex.finditer(t):
            labels=re.findall(r'\\label\{([^}]+)\}',match.group())
            if not labels: continue
            contracts.append({'path':str(path.relative_to(ROOT)),'source_path':row['path'],
                              'labels':labels,'start_char':match.start(),'end_char':match.end(),
                              'first_line':t.count('\n',0,match.start())+1,
                              'last_line':t.count('\n',0,match.end())+1,
                              'text':match.group(),'sha256':digest(match.group().encode())})
    dump('source-contracts.json',contracts)
    specs=[
      ('One-Sample','build/sections/introduction.tex',1,75,'Full-seed theorem and explicit running-time disclaimer'),
      ('One-Sample','build/sections/setup.tex',1,105,'Hidden-vector contract and sample simulation proof'),
      ('One-Sample','build/sections/algorithm.tex',1,10000,'All executed operations, density optimizer, activation schedule, feasibility'),
      ('One-Sample','build/sections/accounting.tex',1,10000,'Pointwise minimum-over-orders payoff and final constant'),
      ('One-Sample','build/sections/secretary.tex',1,10000,'Companion secretary interface: no new implementation primitive'),
      ('Entropy-and','build/sections/01-introduction.tex',1,10000,'Strong entropy theorem, weighted consequences and companion interfaces'),
      ('Entropy-and','build/sections/02-polytope.tex',1,10000,'Actual conditional gluing proof, all face and contraction contracts'),
      ('Entropy-and','build/sections/03-entropy.tex',1,10000,'Trace proof, boundary reduction, componentwise refinement'),
      ('Entropy-and','build/sections/10-examples.tex',1,10000,'Source Klee construction, exact values, existing coefficient obstruction'),
      ('Entropy-and','build/appendices/appendix-b.tex',1,10000,'Nonlinear covariance comparison; not a hidden improved coefficient'),
      ('A-Fully-Polynomial','build/main.tex',120,220,'Uniform FPRAS contract and distinct state-space/weighted comparison'),
      ('A-linear-list','build/sections/01-introduction.tex',1,10000,'Absolute linear list bound and proof strategy'),
      ('A-linear-list','build/sections/03-small-graphs.tex',1,210,'Small graph contract and eligible thinning mechanics'),
      ('A-linear-list','build/sections/03-small-graphs.tex',390,10000,'Global palette partition and final coloring implication'),
      ('A-linear-list','build/sections/04-list-transfer.tex',1,350,'Precoloring constraint budget and global color reservation'),
      ('Correspondence-Coloring','build/sections/introduction.tex',1,10000,'Quantifiers fixed r, maximum degree, and cover convention'),
      ('Correspondence-Coloring','build/sections/adjustment.tex',1,155,'Full partitioned adjustment interface and dual separation proof'),
      ('Correspondence-Coloring','build/sections/rounds.tex',1,105,'Actual maximum-degree normalization and one-round statement'),
      ('Correspondence-Coloring','build/sections/rounds.tex',245,335,'Read-concentration and matching-sum proof interface'),
      ('Correspondence-Coloring','build/sections/completion.tex',1,10000,'Degree-based completion and r-dependent thresholds'),
      ('A-Logarithmic-Independence','build/sections/introduction.tex',1,10000,'Companion independence scope'),
      ('A-counterexample-to-Hadwiger','build/sections/01-introduction.tex',1,85,'Ordinary/fractional counterexample does not supply DP upper bound'),
      ('Exponential-PSD','build/source/sections/introduction.tex',1,10000,'Exact rank theorem, scalar block proof and approximation caveat'),
    ]
    locators=[]
    for prefix,suffix,first,last,purpose in specs:
        rows=[r for r in manifest if r['path'].split('/')[1].startswith(prefix) and r['path'].endswith(suffix)]
        assert len(rows)==1,(prefix,suffix,rows)
        path=str((S/'pinned'/rows[0]['path']).relative_to(ROOT))
        locators.append(slice_record(path,first,last,purpose))
    dump('read-locators.json',locators)
    primary=[]
    for name,first,last,purpose in [
      ('iff-sfm',215,226,'Normalized integer value-oracle setting'),
      ('iff-sfm',565,575,'Theorem 4.2: strongly polynomial SFM'),
      ('strong-secretary',155,184,'Theorem 1.3, fixed-order restriction, O(n^2) independence queries'),
      ('sample-ocrs',92,118,'Almighty adversary, extra prophet-reduction samples, Theorem 1.1'),
      ('sample-prophet',1,105,'Versioned original sample-based prophet comparison'),
      ('dvorak-yepremyan',50,123,'Linear correspondence Hadwiger scope and dense-random-graph theorem'),
      ('dvorak-yepremyan',149,196,'Precise IS-richness definition and Theorem 2.2'),
      ('kaniewski-lee-dewolf',598,627,'Section 7.3, Theorem 19 one-sided error/rank tradeoff'),
    ]:
        primary.append(slice_record(str((S/'literature'/f'{name}.txt').relative_to(ROOT)),first,last,purpose))
    dump('primary-contracts.json',primary)
    tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text())
    fams=sorted({r['path'].split('/')[1] for r in tree['tree'] if len(r['path'].split('/'))>=3})
    dump('inventory.json',{'truncated':tree['truncated'],'entries':len(tree['tree']),
                          'manuscripts':len(fams),'selected_families':sorted({r['path'].split('/')[1] for r in manifest}),
                          'source_files':len(manifest),'source_contracts':len(contracts)})
    dep=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json'
    dump('external-dependencies.json',[{'path':str(dep.relative_to(ROOT)),'sha256':digest(dep.read_bytes()),
                                      'role':'Read-only inventory/hash manifest for the complete text-cache search'}])
    print(json.dumps({'source_contracts':len(contracts),'read_locators':len(locators),'primary_contracts':len(primary),'manuscripts':len(fams)}))
