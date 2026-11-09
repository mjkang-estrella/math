from pathlib import Path
import json,hashlib,os,subprocess
p=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4")
order=json.loads((p/"SOURCE-BASELINE-ORDER.json").read_text())["order"]
order += ["CMDRRIncidenceSums","CMDRRRowOccurrences","CMDRRGameIncidences",
"CMDRRWeightedOccurrences","CMDRRFemalePairs","CMDRRCentralIdentity","CMDRRSingleElimination",
"CMDRRFiveOrbit","CMDRRTranspose","CMDRRRowSigns","CMDRRSigns","CMDRRNonexistence",
"CMDRRColumnCycles","CMDRRSignAPI","CMDRRControls","CMDRRAuditFinal"]
def write(n,s):
    subprocess.run(["python3","-I","-B",str(p/"write_lane.py"),n],input=s,text=True,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
build=p/"extracted-r4/build"
src=p/"extracted-r4/src"
build.mkdir(parents=True,exist_ok=True)
src.mkdir(parents=True,exist_ok=True)
assert not any(build.iterdir())
assert sorted(f.stem for f in (p/"src").iterdir() if f.suffix==".lean")==sorted(order)
hashes={}
for m in order:
    data=(p/"src"/(m+".lean")).read_text()
    write("extracted-r4/src/"+m+".lean",data)
    hashes[m]=sha(p/"src"/(m+".lean"))
    assert hashes[m]==sha(src/(m+".lean"))
env=dict(os.environ)
env["LEAN_PATH"]=str(build)+":"+":".join(env["LEAN_PATH"].split(":")[1:])
assert str(p/"build") not in env["LEAN_PATH"].split(":")
pins=json.loads((p/"PINS.json").read_text())
def run(label,args):
    r=subprocess.run(["timeout","140","python3","-I","-B",str(p/"runner.py"),label,"--",*args],env=env)
    assert r.returncode==0,(label,r.returncode)
for m in order:
    run("replay_strict_"+m,[pins["lean_bin"],"-j1","-M3500","-DwarningAsError=true",
        "-o",str(build/(m+".olean")),str(src/(m+".lean"))])
for m in order:
    run("replay_checker_"+m,[pins["leanchecker_bin"],m])
after={m:sha(src/(m+".lean")) for m in order}
assert after==hashes
assert all(sha(p/"src"/(m+".lean"))==hashes[m] for m in order)
write("results/REPLAY-R4.json",json.dumps(dict(scope="ALL_SOURCE_FULL_ENDPOINT",empty_build_verified=True,
order=order,lean_path=env["LEAN_PATH"],sources_before=hashes,sources_after_checkers=after,
oleans_after_checkers={m:sha(build/(m+".olean")) for m in order},
checks="every strict/checker exit asserted zero, receipt per command"),indent=1)+"\n")
print("FULL_REPLAY_SUCCESS",len(order))
