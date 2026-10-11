"""Create an immutable-first inventory, prevalidate, then seal EXCLUSIVELY once."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PREFIX="frontier/experiments/i176_uniform_five_port_rank/"
SOURCE="frontier/sources/i176_uniform_five_port_rank/"
REPORT="frontier/iterations/i176-uniform-five-port-rank.md"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def entry(path):
    data=(ROOT/path).read_bytes()
    return {"path":path,"sha256":sha(data),"size":len(data)}


def create(path,value):
    with path.open("x") as stream:
        json.dump(value,stream,indent=2,sort_keys=True)
        stream.write("\n")


assert sys.flags.isolated and sys.dont_write_bytecode
mode=sys.argv[1]
if mode=="inventory":
    assert not (HERE/"inventory.json").exists() and not (HERE/"seal.json").exists()
    old=json.loads((ROOT/"frontier/experiments/i175_affected_prism_exterior/inventory.json").read_bytes())
    external={x["path"] for x in old["owned"]+old["external"]}|set(old["controls"])
    external.update({
        "frontier/iterations/i175-affected-prism-exterior-parent-disposition.md",
        "frontier/iterations/iteration176-uniform-five-port-rank-brief.md",
    })
    external.update(str(p.relative_to(ROOT)) for p in (ROOT/"frontier/experiments").glob("i175-parent-*") if p.is_file())
    contexts={x["path"] for x in old["context"]}
    assert not external & contexts
    controls=[PREFIX+x for x in ("inventory.json","prevalidation.json","seal.json")]
    owned={REPORT}
    for prefix in (PREFIX,SOURCE):
        owned.update(str(p.relative_to(ROOT)) for p in (ROOT/prefix).rglob("*") if p.is_file())
    assert not owned & external and not owned & set(controls)
    inv={"iteration":176,"owned":[entry(p) for p in sorted(owned)],
         "external":[entry(p) for p in sorted(external)],
         "context":[dict(entry(x["path"]),I175_historical=x["sha256"]) for x in old["context"]],
         "controls":controls,"policy":"Strict mathematical bytes; current context stability, not historical equality; no ancestor execution",
         "replays":[{"function":name,"payload":PREFIX+filename} for name,filename in [
             ("mandatory","mandatory-attempt-04.json"),("finite","finite-attempt-01.json"),
             ("uniform","uniform-attempt-02.json")]]}
    create(HERE/"inventory.json",inv)
    print(json.dumps({"owned":len(owned),"external":len(external),"contexts":len(contexts)}))
elif mode=="seal":
    assert (HERE/"inventory.json").exists()
    assert not (HERE/"prevalidation.json").exists() and not (HERE/"seal.json").exists()
    run=subprocess.run([sys.executable,"-I","-B",str(HERE/"verify176.py"),"--prevalidate"],capture_output=True)
    if run.returncode or run.stderr:
        # No reseal, and no silent overwrite: retain raw failed prevalidation captures.
        for name,data in [("prevalidation-failure-stdout.json",run.stdout),
                          ("prevalidation-failure-stderr.txt",run.stderr)]:
            with (HERE/name).open("xb") as stream:
                stream.write(data)
        sys.stdout.buffer.write(run.stdout)
        sys.stderr.buffer.write(run.stderr)
        raise SystemExit(run.returncode or 1)
    pre=json.loads(run.stdout)
    assert pre["status"]=="PASS" and pre["prevalidation"] and pre["stderr_empty"]
    create(HERE/"prevalidation.json",pre)
    seal={"iteration":176,"creation":"Exclusive one-time seal after successful prevalidation; never reseal",
          "inventory_sha256":sha((HERE/"inventory.json").read_bytes()),
          "prevalidation_sha256":sha((HERE/"prevalidation.json").read_bytes()),
          "report_sha256":sha((ROOT/REPORT).read_bytes()),
          "verifier_sha256":sha((HERE/"verify176.py").read_bytes())}
    create(HERE/"seal.json",seal)
    print(json.dumps({"status":"SEALED_ONCE","prevalidation_seconds":pre["runtime_seconds"],
                      "report_sha256":seal["report_sha256"],"verifier_sha256":seal["verifier_sha256"],
                      "seal_sha256":sha((HERE/"seal.json").read_bytes())},indent=2))
else:
    raise SystemExit("expected inventory or seal")
