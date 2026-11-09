from pathlib import Path
import hashlib, json, subprocess
p=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4")
def sha(f): return hashlib.sha256(f.read_bytes()).hexdigest()
receipts=[]
for f in sorted((p/"receipt").iterdir()):
    if f.suffix==".json":
        d=json.loads(f.read_text())
        receipts.append(dict(path=str(f.relative_to(p)),sha256=sha(f),**d))
modules=[]
for f in sorted((p/"src").iterdir()):
    if f.suffix==".lean":
        m=f.stem
        rr=[r for r in receipts if r["label"]=="lean_"+m]
        modules.append(dict(module=m,source_sha256=sha(f),olean_sha256=sha(p/"build"/(m+".olean")) if (p/"build"/(m+".olean")).is_file() else None,latest_strict=rr[-1] if rr else None))
data=dict(status="FULL_ENDPOINT_CHECKED_GATES_PENDING",credit=0,campaign=55,target=60,previous=39,modules=modules,receipts=receipts,
unpaid=["Full endpoint DAG audit, controls, replay, paper and independent acceptance"],
process=dict(r3_breach="UNRESOLVED/UNACCEPTED, missing normal receipt/reap evidence",display_exception="Root authorized prospective standalone timeout20 reader with affinity<=2, CPU10, AS512MiB before reads; only named own logs; no sampled group/native UI telemetry; not compiler-runner execution",source_reads="immutable runner",baseline="22 production + audit freshly compiled in recorded order; no old oleans copied"))
def write(n,s): subprocess.run(["python3","-I","-B",str(p/"write_lane.py"),n],input=s,text=True,check=True)
write("results/326555.json",json.dumps(data,indent=1)+"\n")
write("CHECKPOINT.md","# Full literal endpoint strict checked, credit 0\n\nBaseline 22 production modules and audit cold compiled in mandated order. Central A+B=1+z, B+z=2, arbitrary two-cycle elimination, single-row five-cycles, swapped row/column correspondence and U/C/T sign contradiction are strict checked. CMDRRNonexistence proves canonical_noSource, noSource_five_three and universalExistsFiveThree_negation. Exact source/olean/receipt hashes and exits are in results/326555.json.\n\nFinal whole-environment/closure audit, controls, source-only replay, checker and paper gates remain pending; independent review/root acceptance unpaid. r3 process breach remains unresolved/unaccepted. Standalone own-log displays use the prospective root exception; they have no sampled group or native UI telemetry and did not run through the compiler runner. Campaign 55/60 beyond 39.\n")
print("CHECKPOINT RECORDED",len(modules),len(receipts))
