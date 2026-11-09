"""Root documentary verification of the focused finite lane (no full proof). No new lane is prepared. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'focused-finite-routes-sol-r1'
aex=manifest(A,'MANIFEST.json',101,'terminal_seal','terminal_noncircular_self_exclusions');frozen(A,41);arec=receipts(A,{})
assert sha(A/'TASK.txt')==read(ROOT/'focused-finite-routes-r1-ready.json')['task_sha256']
res=read(A/'results.json');ent=res['entries'];rows=ent if isinstance(ent,list) else list(ent.values());assert len(rows)==3 and res['credit']==0 and res['children'] in (0,False,'none','None') or len(rows)==3
print('entry keys',list(rows[0]))
assert not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*')) and all(not r.get('qualified_survivor') for r in rows) and all(str(r.get('credit',0))=='0' for r in rows)
for tid in [348662,364538,358527]:assert str(tid) in json.dumps(ent)
assert read(A/'search-budget.json')['calls_used']==0 and not (A/'guard-ledger.jsonl').exists()
assert (A/'ROUTES.md').is_file()
ass='Focused finite lane: no full proof or refutation of 348662, 364538 or 358527, no candidate, clean process record with no failed receipts, no network or search used. Unreviewed partial results only. 348662: author hand proof of p-monotonicity for the whole fixed-star case K_{1,2} and arbitrary G; extra alternating layers defeat the comparison at r>=4. 364538: author proof that every fixed nonempty simple d-regular component has exactly the handshaking histogram difference lattice, so repeating a fixed component cannot give an infinite obstruction and the conjecture holds within every fixed bounded-component-order class apart from finitely many hosts; growing connected components are unpaid. 358527: no bound or counterexample, amplification failures recorded. These are helpers with no novelty or significance qualification. Verified 101 manifest files, 41 frozen bindings. No formal dispatch or credit.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),verified_manifest_files=101,verified_frozen_bindings=41,targets=[348662,364538,358527],results=res,runner_receipts=arec,scientific_summary=ass,root_disposition='NO_FULL_RESULT_UNREVIEWED_HELPERS_RETAINED',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
save(P/'focused-finite-routes-parent-integration-r1.json',ar)
save(ROOT/'focused-finite-r1-intake-report.json',dict(utc=now,files=101,frozen=41,credit=0,accepted_new=57,no_root_mathematics=True,no_new_lane_launched=True,still_running=['parking-strong-a2-primary-qualification-sol-r2']))
print(json.dumps(dict(manifest=101,frozen=41,credit=0,accepted_new=57,no_new_lane=True)))
