"""Development runner: freezes each attempt, retains stdout/stderr and failed stages."""
import hashlib
import json
from pathlib import Path
import sys
import time
import traceback
from fractions import Fraction

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
OWN = ROOT/"frontier/experiments/i178_five_port_annihilator"


def encode(x):
    return (json.dumps(x,sort_keys=True,indent=2,default=lambda v:
                       str(v) if isinstance(v,Fraction) else (_ for _ in ()).throw(TypeError(type(v))))
            +"\n").encode()


def main():
    role, attempt = sys.argv[1:]
    prefix = f"{role}-attempt-{attempt}"
    binding = json.loads((OWN/"inputs.json").read_bytes())
    memory = {}
    for r in binding["strict"]:
        data = (ROOT/r["path"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == r["sha256"], r["path"]
        assert len(data) == r["size"]
        memory[r["path"]] = data
    context = {r["path"]:(ROOT/r["path"]).read_bytes() for r in binding["context"]}
    source = {}
    for name in ("math178.py","research178.py","run178.py"):
        data = (OWN/name).read_bytes()
        source[name] = data
        (OWN/(prefix+"-"+name+".disabled")).write_bytes(data)
    manifest = {"inputs_sha256":hashlib.sha256((OWN/"inputs.json").read_bytes()).hexdigest(),
                "source":{k:hashlib.sha256(v).hexdigest() for k,v in source.items()},
                "context":{k:hashlib.sha256(v).hexdigest() for k,v in context.items()}}
    with (OWN/(prefix+"-preflight.json")).open("x") as f:
        json.dump(manifest,f,sort_keys=True,indent=2)
        f.write("\n")
    started = time.perf_counter()
    stdout, stderr, code = b"",b"",0
    try:
        ns = {"__name__":"i178_diagnostic"}
        for name in ("math178.py","research178.py"):
            exec(compile(source[name],str(OWN/name),"exec"),ns)
        def load(path):
            assert not path.endswith((".py",".disabled"))
            return json.loads(memory[path])
        stdout = encode(ns[role](load))
        for r in binding["strict"]:
            assert (ROOT/r["path"]).read_bytes() == memory[r["path"]]
        for path,data in context.items():
            assert (ROOT/path).read_bytes() == data
    except Exception:
        stderr = traceback.format_exc().encode()
        code = 1
    for suffix,data in [(".json",stdout),("-stderr.txt",stderr)]:
        with (OWN/(prefix+suffix)).open("xb") as f:
            f.write(data)
    receipt = {"returncode":code,"seconds":time.perf_counter()-started,
               "stdout_sha256":hashlib.sha256(stdout).hexdigest(),
               "stderr_sha256":hashlib.sha256(stderr).hexdigest()}
    with (OWN/(prefix+"-receipt.json")).open("x") as f:
        json.dump(receipt,f,sort_keys=True,indent=2)
        f.write("\n")
    print(json.dumps(receipt,sort_keys=True))
    if stderr:
        print(stderr.decode(),file=sys.stderr)
    sys.exit(code)


if __name__ == "__main__":
    main()
