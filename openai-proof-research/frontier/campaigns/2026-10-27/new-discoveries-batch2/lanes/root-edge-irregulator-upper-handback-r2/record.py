import datetime, hashlib, json, math, zipfile
from fractions import Fraction
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;cwd=B.parents[4]
U=P.parent/'sol-edge-irregulator-upper-formal-r2';S=P.parent/'sol-fresh-source-discovery-r78'
Q=P.parent/'root-fresh-source-r78-handback';Q.mkdir(exist_ok=True)
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return h.hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
manifest=json.loads((U/'manifest.json').read_text())
archive=U/'upper-witness-component.zip'
assert sha(archive)=='4d62461a62577e5b2d77045eb2d228814c7481c90b24d45d85383c0313e2d641'
with zipfile.ZipFile(archive) as z:
    assert not any(n.endswith(('.olean','.ilean','.o')) for n in z.namelist())
    for n,h in manifest.items():
        assert sha(U/n)==h,n
        d=hashlib.sha256()
        with z.open(n) as f:
            for c in iter(lambda:f.read(1048576),b''):d.update(c)
        assert d.hexdigest()==h,n
for n in ('Source','Boundary','Gadget','Edges','Degrees'):
    assert sha(U/'formal'/f'{n}.lean')==sha(P.parent/'sol-edge-irregulator-source-formal-r1/formal'/f'{n}.lean')
receipt=json.loads((U/'verification-fresh/replay-receipt.json').read_text())
assert receipt['declaration_count']==117
record={'utc':now,'status':'UPPER_COMPONENT_INSPECTED_INTEGRATION_PENDING','credit':0,'counts':[7,37],
 'archive_sha256':sha(archive),'manifest_verified':len(manifest),
 'root_read':'Complete UpperWitness, UpperDegrees and Upper sources plus SUMMARY. Actual selected edges0,2,6, cardinality3t, recomputed neighbors/degrees and retained-edge classification prove Valid for t>=2. No residual lower-bound premise.',
 'inherited_five_sources_identical':True,'worker_replay_declarations':117,
 'root_replay_scope':'Prior root extraction replay certified lower/source10modules136declarations. This upper component not separately root recompiled; final combined extraction replay remains required.',
 'integration_lane':'sol-edge-irregulator-manuscript-packet-r1',
 'integration':'Combine minimum_lower and Upper.minimum_upper by antisymmetry, preserve source_refutation and transport. Paper and deterministic integrated source packet delegated.',
 'limitations':'Early Python launcher lacked independent group RSS/wall supervision; later/final extraction supervised. Preserve worker SUMMARY/probes; no cap raises. No acceptance.'}
(P/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
prov=json.loads((S/'provenance.json').read_text())
files=prov['artifact_sha256']
bad=[n for n,h in files.items() if sha(S/n)!=h]
assert not bad,bad
# Independent rational arithmetic for the two failed generic routes and
# the top coefficient of the already-public (3,4) expression; no grading enumeration.
assert Fraction(math.factorial(5), math.factorial(4)*math.factorial(3))==Fraction(5,6)
assert Fraction(24*math.factorial(6),math.factorial(5)**2)==Fraction(6,5)
assert Fraction(math.factorial(4),math.factorial(3)*math.factorial(4))==Fraction(1,6)
assert 4*4==16 and 16*math.factorial(3)==96
adopt={'utc':now,'status':'UNRESOLVED','credit':0,'counts':[7,37],
 'root_read':'Full SUMMARY/discovery; source equivalence retained as proposed helper, not a source resolution or independent primary-body certification.',
 'gap':'For actual tight-grading polynomial N_(i,j), coefficientwise min(i,j)! divisibility remains unproved uniformly. Full C4 not solved.',
 'root_exact_checks':'Artificial integer-valued polynomial scaled top5/6, Poisson bracket scaled coefficient6/5, singleton scaled coefficient1/6 versus public full polynomial scaled top16 (N top96) checked exactly. No source counterexample.',
 'worker_grading_enumeration_not_root_replayed':True,
 'manifest_verified':len(files),'manifest_mismatches':bad,
 'freshness':'Worker observed Omega75fa71fb84c19580a0ea89b3dc7c8158f7aa7446 at17:56UTC beyond full70af5407 inventory; no new complete delta audit. HOLD retained.',
 'all_file_hashes':{str(f.relative_to(S)):sha(f) for f in sorted(S.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}}
(Q/'ADOPTION.json').write_text(json.dumps(adopt,indent=2)+'\n')
nf=B/'NEXT.md';t=nf.read_text()
t=t.replace('charges and source vertex transport are closed. Upper witness still running;\npaper/final review/acceptance remain. Credit0. See', 'charges and source vertex transport are closed. Upper witness completed with\n117-declaration worker replay; root inspected actual sources and verified archive.\nCombined exact minimum, manuscript and audited packet delegated. Credit0. See')
t=t.replace('Active Sol high/default: edge-irregulator upper-witness formal r2,\nfresh finite/algebra discovery r78 and fresh analytic discovery r79.', 'r78 cluster-scattering C4 remains unresolved: uniform factorial divisibility\nmissing, bounded cancellation evidence only; current Omega advanced, freshnessHOLD.\nActive Sol high/default: edge-irregulator manuscript/packet r1,\nfresh analytic discovery r79 and fresh finite/arithmetic discovery r80.')
nf.write_text(t)
for out,folders,extra in [(Q,(S,Q),[]),(P,(U,P),[nf])]:
    paths=[]
    for folder in folders:
        for f in sorted(folder.rglob('*')):
            if not f.is_file() or '__pycache__' in f.parts or 'verification-fresh' in f.parts:continue
            if f.suffix in ('.olean','.ilean','.o') or f.name=='pathspec.txt':continue
            paths.append(str(f.relative_to(cwd)))
    paths.extend(str(f.relative_to(cwd)) for f in extra)
    (out/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'upper_manifest_PASS':len(manifest),'r78_manifest_PASS':len(files),'root_diagnostics':'PASS','counts':[7,37]}))
