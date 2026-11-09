"""Generic root preparation of a first Lean lane after a qualification. Arguments: mathdb_id qualification_lane new_lane body_file ready_name model_label peer1 peer2. No root Lean or mathematics."""
import os,resource,subprocess,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
mid,ql,nl,bodyf,rname,label,p1,p2=sys.argv[1:9];now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json')
Q=P/ql;T=P/'transitive-bunkbed-endpoint-assembly-formal-deepseek-r23';L=P/nl;assert not L.exists();L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:copy(T/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'))
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir()
for rel,q in {'inputs/reviewer-PROOF.md':Q/'PROOF.md','inputs/reviewer-REVIEW.md':Q/'REVIEW.md','inputs/author-candidate.md':Q/'inputs/author-candidate.md','inputs/author-formal-plan.md':Q/'inputs/author-formal-plan.md',f'inputs/literal{mid}.json':Q/f'inputs/literal{mid}.json'}.items():copy(q,rel)
(L/'inputs/sources').mkdir()
for q in sorted(set((Q/'inputs/sources').glob('*'))|set((Q/'sources').glob('*.pdf'))):
 if q.is_file() and q.suffix in ('.pdf','.txt'):copy(q,'inputs/sources/'+q.name)
for q in list((L/'inputs/sources').glob('*.pdf')):
 tx=q.with_suffix('.txt')
 if not tx.exists():
  r=subprocess.run(['pdftotext','-layout',str(q),str(tx)],capture_output=True);assert r.returncode==0,r.stderr
save(L/'INPUT-ORIGINS.json',origins)
(L/'TASK.txt').write_text(Path(bodyf).read_text().replace('{L}',str(L)).replace('{P1}',p1).replace('{P2}',p2))
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=int(mid),task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model=label,credit=0,accepted_new=led['accepted_new'],target_new=led['target_new'],protected_peers=[p1,p2])
save(ROOT/rname,ready);save(ROOT/('selection-routing-'+rname),dict(ids=[int(mid)],sources=[],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps({k:ready[k] for k in ['lane','task_sha256','frozen_bindings']}))
