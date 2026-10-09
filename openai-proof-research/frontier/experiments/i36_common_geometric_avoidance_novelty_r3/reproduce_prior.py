"""Run unchanged R2 (which runs unchanged author), capturing R2's sole write."""
from pathlib import Path
import contextlib, hashlib, io, json, runpy, sys
sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parents[3]
R2=ROOT/'frontier/experiments/i36_common_geometric_avoidance_r2'
def reproduce():
    monitored=[]
    for name in ('i36_harmonic_analysis_discovery','i36_common_geometric_avoidance_r2'):
        for kind in ('sources','experiments'):
            monitored += [p for p in (ROOT/'frontier'/kind/name).rglob('*') if p.is_file() and '__pycache__' not in p.parts]
    monitored += [ROOT/'frontier/iterations/i36-harmonic-analysis-discovery.md',ROOT/'frontier/reviews/i36-common-geometric-avoidance-r2.md']
    before={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in monitored}
    original=Path.write_text; captured=[]; stdout=io.StringIO()
    def intercept(p,data,*a,**kw):
        assert p.resolve()==R2/'verification.json', str(p)
        captured.append(data); return len(data)
    sys.path.insert(0,str(R2))
    try:
        Path.write_text=intercept
        with contextlib.redirect_stdout(stdout): runpy.run_path(str(R2/'verify.py'),run_name='__main__')
    finally:
        Path.write_text=original;sys.path.pop(0)
    assert captured==[stdout.getvalue()]
    assert all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h for p,h in before.items())
    return {'status':'PASS','monitored_files_unchanged':len(before),'method':'R2 original __file__ and source; sole verification.json write captured; R2 internally captures author sole write. No seals regenerated.','result':json.loads(stdout.getvalue()),'before_after_sha256':before}
if __name__=='__main__': print(json.dumps(reproduce(),indent=2,sort_keys=True))
