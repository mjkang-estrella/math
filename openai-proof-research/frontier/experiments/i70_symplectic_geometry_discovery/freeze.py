"""One-time author acquisition. Writes only the I70 source directory; not the verifier."""
from pathlib import Path
import collections, datetime, hashlib, json, shutil, subprocess

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT/'frontier/sources/i70_symplectic_geometry_discovery'
CORPUS = ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def dump(p, x):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(x, indent=2, sort_keys=True)+'\n')

def main():
    if (OUT/'frozen-inputs.json').exists():
        raise SystemExit('Refusing to refresh an existing freeze')
    ledgers = ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
    refs = ['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md',
      'frontier/iterations/i07-structures.md','frontier/iterations/i15-odd-order-topology.md',
      'frontier/iterations/i15-odd-order-topology-resumed.md',
      'frontier/reviews/i15-odd-order-topology-novelty-r3.md',
      'frontier/iterations/i19-fresh-structural-discovery.md',
      'frontier/iterations/i21-signed-saxl-dominance.md',
      'frontier/iterations/i24-elementary-unimodality-resumed.md',
      'frontier/iterations/i28-algebra-discovery.md',
      'frontier/reviews/i68-logarithmic-blowup-novelty.md',
      'frontier/experiments/i68_logarithmic_blowup_novelty/verify.py']
    refs += [str(p.relative_to(ROOT)) for p in (ROOT/'frontier/findings').glob('R*.md')
             if p.name[:4] in ['R006','R008','R009','R010','R011','R012','R013','R014']]
    records=[]
    for f in ledgers+refs:
        p=ROOT/f; b=p.read_bytes()
        snapshot=None
        if f in ledgers or f in ['AGENTS.md','sources/upstream.json','sources/preprints-tree.json']:
            snapshot='inputs/'+f
            q=OUT/snapshot; q.parent.mkdir(parents=True,exist_ok=True); q.write_bytes(b)
        records.append(dict(path=f,sha256=sha(b),size=len(b),mutable=f in ledgers,snapshot=snapshot))
    tree=json.loads((ROOT/'sources/preprints-tree.json').read_text())
    entries={x['path']:x for x in tree['tree'] if x['type']=='blob'}
    titles=[x['path'] for x in tree['tree'] if x['type']=='tree' and x['path'].count('/')==1]
    paths=subprocess.check_output(['rg','--files','--no-ignore'],cwd=CORPUS,text=True).splitlines()
    inventory=[]
    for f in sorted(paths):
        b=(CORPUS/f).read_bytes(); actual=blob(b)
        assert f in entries and actual==entries[f]['sha'], f
        inventory.append(dict(path=f,size=len(b),sha256=sha(b),git_blob=actual))
    prefixes=['A-counterexample-to-the-nearby-Lagrangian',
      'Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number',
      'Sharpness-of-the-Cyclic-Integral-Floer','Symplectic-Ball-Packings',
      'Symplectic-Balls-in','A-degenerate-counterexample-to-the-critical-number-Arnold',
      'A-nondegenerate-counterexample-to-the-Morse-number-Arnold',
      'The-symmetric-Mahler-conjecture-and-its-equality-cases','The-Mahler-Conjecture-for-General']
    selected=[r for r in inventory if any(r['path'].split('/')[1].startswith(s) for s in prefixes)]
    for r in selected:
        p=OUT/'pinned'/r['path']; p.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(CORPUS/r['path'],p)
        r['raw_url']=f"https://raw.githubusercontent.com/openai/math/{PIN}/{r['path']}"
    queries={
      'packing_relative':r'(?i)(relative.{0,45}pack|prescrib.{0,45}ball|space.{0,40}symplectic.{0,30}embed|packing.{0,40}isotop|symplectic.{0,30}unknott)',
      'packing_operations':r'(?i)(Hamiltonian comparison|surface packing|outer.face|polar.packings|reserved.{0,20}ball|central.{0,20}ball)',
      'fixed_points':r'(?i)(stable Morse|cyclic.{0,25}Floer|mixed.prime torsion|short.{0,15}period)',
      'lagrangian':r'(?i)(nearby Lagrangian|tube torsion|one.critical|stable tube|homogeneous data)',
      'quantitative_relative':r'(?i)(packing stability|relative.{0,20}Moser|Hofer.{0,25}(norm|energy)|parametric.{0,20}symplectic)'}
    searches=[]
    for key,pattern in queries.items():
        cmd=['rg','--no-ignore','--line-number','--with-filename','--color','never','-e',pattern,'.']
        proc=subprocess.run(cmd,cwd=CORPUS,text=True,capture_output=True)
        assert proc.returncode in (0,1)
        lines=sorted(proc.stdout.splitlines()) # multiset: preserve every occurrence
        searches.append(dict(name=key,argv=cmd,returncode=proc.returncode,lines=lines,stderr=proc.stderr))
    dump(OUT/'searches.json',dict(domain='frontier/sources/i14_spectral_width_novelty_r3/corpus',domain_files=len(paths),searches=searches))
    dump(OUT/'corpus-inventory.json',inventory)
    dump(OUT/'pins.json',dict(commit=PIN,files=selected))
    dump(OUT/'catalogue-screen.json',dict(tree_entries=len(tree['tree']),manuscripts=len(titles),
      relevant_titles=[x for x in titles if any(w in x.lower() for w in ['symplec','lagrang','floer','hamilton','packing','mahler','arnold'])]))
    dump(OUT/'frozen-inputs.json',dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=records))
    print(json.dumps(dict(corpus_files=len(paths),tree_entries=len(tree['tree']),manuscripts=len(titles),pins=len(selected),search_lines={r['name']:len(r['lines']) for r in searches})))

if __name__=='__main__': main()
