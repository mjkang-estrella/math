import datetime, hashlib, itertools, json, zipfile
from fractions import Fraction
from pathlib import Path

P=Path(__file__).resolve().parent
B=P.parent.parent
cwd=B.parents[4]
F=P.parent/'sol-edge-irregulator-source-formal-r1'
S=P.parent/'sol-fresh-source-discovery-r77'
Q=P.parent/'root-fresh-source-r77-handback'
Q.mkdir(exist_ok=True)
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''): h.update(c)
    return h.hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
manifest=json.loads((F/'manifest.json').read_text())
bad=[n for n,h in manifest.items() if sha(F/n)!=h]
assert not bad,bad
archive=F/'edge-irregulator-component.zip'
assert sha(archive)=='74e2c9ead42007930c623531d4ee290865cf41d245f520ca7bff8270a9fd2f74'
with zipfile.ZipFile(archive) as z:
    for n,h in manifest.items():
        a=hashlib.sha256()
        with z.open(n) as f:
            for c in iter(lambda:f.read(1048576),b''): a.update(c)
        assert a.hexdigest()==h,n
    assert not any(n.endswith(('.olean','.ilean','.o')) for n in z.namelist())
receipt=json.loads((F/'verification-fresh/replay-receipt.json').read_text())
result={'utc':now,'status':'COMPONENT_ONLY_SOURCE_INCOMPLETE','credit':0,'counts':[7,37],
 'root_inspection':'Read full SUMMARY, Source/Boundary/Degrees and gadget/edge interfaces. Checked archive bytes, all manifest entries and absence of prebuilt proof artifacts. No independent root Lean replay this handback.',
 'manifest_entries_verified':len(manifest),'archive_sha256':sha(archive),
 'worker_receipt_sha256':sha(F/'verification-fresh/replay-receipt.json'),
 'remaining':['general retained-degree identification and global deletion lower bound','explicit upper witness','finite vertex transport','unconditional source negation'],
 'parallel_assignments':{'sol-edge-irregulator-lower-source-formal-r2':'General deletion bound, transport and source negation; independent of upper witness.','sol-edge-irregulator-upper-formal-r2':'Actual deletion witness, all degrees, Valid and cardinality; no source negation claim.'},
 'limits':'Worker five-module/89-declaration replay preserved as component evidence, not full formal PASS. Source, bounded novelty and ordinary proof adoption unchanged.'}
(P/'ADOPTION.json').write_text(json.dumps(result,indent=2)+'\n')

functions=list(itertools.product(*[range(1,i+1) for i in range(1,5)]))
def blocks(f):
    return tuple(frozenset(i+1 for i,x in enumerate(f) if x==v) for v in sorted(set(f)))
def minima(f): return frozenset(min(b) for b in blocks(f))
lower=[f for f in functions if minima(f)=={1,3}]
upper=[f for f in functions if minima(f)=={1,2,3}]
def refines(u,l): return all(any(b<=a for a in blocks(l)) for b in blocks(u))
badclass=[f for f in lower if frozenset({3,4}) in blocks(f)]
neighbors=[u for u in upper if any(refines(u,l) for l in badclass)]
assert len(functions)==24 and len(lower)==4 and len(upper)==3
assert len(badclass)==2 and neighbors==[(1,2,3,3)]
for l in range(1,21): assert Fraction(1,2)**l>Fraction(1,3)**l
prov=json.loads((S/'provenance.json').read_text())
mismatches=[n for n,v in prov['files'].items() if sha(S/n)!=v['sha256']]
adopt={'utc':now,'status':'UNRESOLVED','credit':0,'counts':[7,37],
 'root_read':'Full SUMMARY and discovery; source scope all n>=1 and integer l>1 PECK, no independent primary-body refresh in this handback.',
 'root_exact_checks':{'functions':24,'lower_fiber':lower,'upper_fiber':upper,'obstructed_lower_class':badclass,'upper_neighbors':neighbors,'tensor_mass_obstruction_l1_through20':True},
 'interpretation':'Conditional uniform fiber refinement coupling is impossible, not a counterexample to PECK or global normalized matching. Full strong-Sperner argument remains unproved.',
 'manifest_entries':len(prov['files']),'manifest_mismatches':mismatches,
 'worker_flow_suite_not_root_replayed':True,
 'all_file_hashes':{str(f.relative_to(S)):sha(f) for f in sorted(S.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}}
(Q/'ADOPTION.json').write_text(json.dumps(adopt,indent=2)+'\n')
nf=B/'NEXT.md'
t=nf.read_text().replace('Formal investment begins in sol-edge-irregulator-source-formal-r1; credit0.', 'Initial formal component replay passes five modules/89 declarations, but the\nunconditional source negation remains absent. Continuation split into global\nlower bound/source transport and explicit upper witness; credit0. See\nroot-edge-irregulator-component-handback-r1/ADOPTION.json.')
t=t.replace('Active Sol high/default: edge-irregulator source formal r1, fresh finite/algebra r77,\nand silicosis preliminary review r1.', 'r77 PECK remains unresolved; root exact fiber-coupling obstruction checked,\nnot a source counterexample. See root-fresh-source-r77-handback/ADOPTION.json.\nActive Sol high/default: edge-irregulator lower/source formal r2, upper-witness\nformal r2, and silicosis preliminary review r1.')
nf.write_text(t)
for out,folders,extra in [(Q,(S,Q),[]),(P,(F,P),[nf])]:
    paths=[]
    for folder in folders:
        for f in sorted(folder.rglob('*')):
            if not f.is_file() or '__pycache__' in f.parts or 'verification-fresh' in f.parts: continue
            if f.suffix in ('.olean','.ilean','.o') or f.name=='pathspec.txt': continue
            paths.append(str(f.relative_to(cwd)))
    paths.extend(str(f.relative_to(cwd)) for f in extra)
    (out/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'archive_manifest_PASS':len(manifest),'PECK_exact_PASS':True,'PECK_manifest_entries':len(prov['files']),'mismatches':mismatches,'counts':[7,37]}))
