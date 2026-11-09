from pathlib import Path
import hashlib,json,re,subprocess
p=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4")
log=p/"logs/1794121038125243263_lean_CMDRRAuditFinal.log"
text=log.read_text()
env=[];prod=[];nodes=[];closures={};axs={}
for line in text.splitlines():
    if "ENV_DECL " in line: env.append(line.split("ENV_DECL ",1)[1])
    if "PRODUCTION " in line:prod.append(line.split("PRODUCTION ",1)[1])
    if "BODY_NODE " in line:nodes.append(line.split("BODY_NODE ",1)[1])
    if "ENDPOINT_CLOSURE " in line:
        s=line.split("ENDPOINT_CLOSURE ",1)[1];name,body=s.split(" ",1)
        closures[name]=body
    if "ENDPOINT_AXIOMS " in line:
        s=line.split("ENDPOINT_AXIOMS ",1)[1];name,body=s.split(" ",1);axs[name]=body
assert len(closures)==15,len(closures)
assert "CMDRR.universalExistsFiveThree_negation" in closures
closures={m.group(1):[n.strip() for n in m.group(2).split(",") if n.strip()] for m in re.finditer(r"ENDPOINT_CLOSURE (\S+) \[(.*?)\]",text,re.S)}
assert len(closures)==15
for root,items in closures.items():
    assert root in items,(root,items[:2])
    assert len(items)>100
required=["CMDRR.Source","CMDRR.A","CMDRR.B","CMDRR.z","CMDRR.Source.central_incidence_identity","CMDRR.Source.B_add_z_of_single_twoCycle","CMDRR.Source.no_single_twoCycle","CMDRR.Source.single_row_five","CMDRR.Source.swapped_U_is_C","CMDRR.Source.U_sign","CMDRR.Source.C_sign","CMDRR.Source.T_sign","CMDRR.Source.canonical_transport"]
assert all(n in closures["CMDRR.universalExistsFiveThree_negation"] for n in required)
summary=dict(log=str(log.relative_to(p)),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
whole_environment_declarations=len(env),production_declarations=len(prod),reachable_body_nodes=len(nodes),
endpoint_closure_counts={n:len(body) for n,body in closures.items()},
endpoint_axiom_unions=axs,production_axiom_gate="Compiler audit throws on any axiom outside propext/Classical.choice/Quot.sound",
scope="environment-wide origin inventory; body/type DAG for all production declarations; exact individual endpoint closures, including private/generated and opaque body dependencies")
def write(n,s):subprocess.run(["python3","-I","-B",str(p/"write_lane.py"),n],input=s,text=True,check=True)
write("audit/FINAL-AUDIT-SUMMARY.json",json.dumps(summary,indent=1)+"\n")
write("audit/ENDPOINT-CLOSURES.json",json.dumps(closures,indent=1)+"\n")
replay=json.loads((p/"results/REPLAY-R4.json").read_text())
print(json.dumps(summary,indent=1))
print("REPLAY",len(replay["order"]),replay["scope"],replay["empty_build_verified"])
