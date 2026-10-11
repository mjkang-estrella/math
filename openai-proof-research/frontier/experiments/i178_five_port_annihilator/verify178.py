"""Read-only sealed replay; Python audit policy, explicitly not an OS sandbox."""
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import types
from fractions import Fraction

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
REL = "frontier/experiments/i178_five_port_annihilator/"
OWN = ROOT/REL
REPORT = "frontier/iterations/i178-five-port-annihilator.md"
SOURCE = ROOT/"frontier/sources/i178_five_port_annihilator"
CONTEXT = {"README.md","frontier/README.md","frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    def exact(obj):
        if isinstance(obj,Fraction):
            return str(obj)
        raise TypeError(type(obj))
    return (json.dumps(value,indent=2,sort_keys=True,default=exact)+"\n").encode()


def members():
    paths = {REPORT}
    for directory in (OWN,SOURCE):
        for p in directory.rglob("*"):
            assert not p.is_symlink(), str(p)
            if p.is_file():
                paths.add(str(p.relative_to(ROOT)))
    return paths


def main():
    start = time.perf_counter()
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    assert prevalidate or not sys.argv[1:]
    invbytes = (OWN/"inventory.json").read_bytes()
    inv = json.loads(invbytes)
    before_members = members()
    owned = {r["path"]:r for r in inv["owned"]}
    assert set(inv["controls"]) == {REL+n for n in ("inventory.json","prevalidation.json","seal.json")}
    required_controls = {REL+"inventory.json"} if prevalidate else set(inv["controls"])
    assert before_members == set(owned) | required_controls
    assert {r["path"] for r in inv["context"]} == CONTEXT
    memory = {}
    for r in inv["owned"]+inv["external"]:
        p = ROOT/r["path"]
        assert not p.is_symlink()
        data = p.read_bytes()
        assert len(data) == r["size"] and sha(data) == r["sha256"], r["path"]
        memory[r["path"]] = data
    current_context = {p:(ROOT/p).read_bytes() for p in CONTEXT}
    control_memory = {p:(ROOT/p).read_bytes() for p in required_controls}
    assert control_memory[REL+"inventory.json"] == invbytes
    if not prevalidate:
        seal = json.loads(control_memory[REL+"seal.json"])
        pre = json.loads(control_memory[REL+"prevalidation.json"])
        assert seal["inventory_sha256"] == sha(invbytes) == pre["inventory_sha256"]
        assert seal["prevalidation_sha256"] == sha(control_memory[REL+"prevalidation.json"])
        assert seal["report_sha256"] == sha(memory[REPORT]) == pre["report_sha256"]
        assert seal["verifier_sha256"] == sha(memory[REL+"verify178.py"]) == pre["verifier_sha256"]
        assert pre["status"] == "PASS" and pre["prevalidation"]
        assert len(pre["probes"]) == 8 and all(p["blocked"] for p in pre["probes"])
        assert len(pre["comparisons"]) == 2 and all(p["byte_identical"] for p in pre["comparisons"])
    source = {str(OWN/name):memory[REL+name] for name in ("math178.py","research178.py")}
    # This inert code object is used only to prove rejection of an outside exec.
    outside_code = compile("pass","<i178-outside-probe>","exec")
    allowed_code = set()
    def remember(code):
        allowed_code.add(code)
        for value in code.co_consts:
            if isinstance(value,types.CodeType):
                remember(value)
    readable = {str(ROOT/p) for p in memory.keys() | current_context.keys() | control_memory.keys()}
    owned_directories = {str(OWN),str(SOURCE)}
    owned_directories |= {str(p.parent) for d in (OWN,SOURCE) for p in d.rglob("*")}
    class Blocked(PermissionError):
        pass
    def guard(event,args):
        if event == "open":
            path,mode,flags = args
            if isinstance(path,int):
                raise Blocked("unbound file descriptor")
            if flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
                raise Blocked("write")
            if os.path.abspath(os.fsdecode(path)) not in readable:
                raise Blocked("unbound-read")
        if event in {"os.remove","os.rename","os.mkdir","os.rmdir","os.chmod","os.chown",
                     "os.link","os.symlink","os.truncate","os.utime","os.chdir",
                     "shutil.copyfile","shutil.rmtree"}:
            raise Blocked("filesystem mutation")
        if event.startswith(("socket.","subprocess.","os.exec","os.spawn","os.fork")) or event == "os.system":
            raise Blocked("network/process")
        if event in {"os.scandir","os.listdir"}:
            if os.path.abspath(os.fsdecode(args[0])) not in owned_directories:
                raise Blocked("unbound-directory")
        if event == "compile":
            raw,filename = args
            if isinstance(raw,str):
                raw = raw.encode()
            if filename not in source or raw != source[filename]:
                raise Blocked("unbound or forged compilation")
        if event == "exec" and args[0] not in allowed_code:
            raise Blocked("unbound execution")
        if event.startswith("ctypes."):
            raise Blocked("native execution")
    sys.addaudithook(guard)
    probes = []
    def blocked(name,fn):
        try:
            fn()
        except Blocked:
            probes.append({"probe":name,"blocked":True})
        else:
            raise AssertionError("probe escaped: "+name)
    blocked("write",lambda: open(OWN/"__blocked_write__","wb"))
    blocked("mutation",lambda: os.mkdir(OWN/"__blocked_directory__"))
    blocked("network",lambda: socket.socket())
    blocked("subprocess",lambda: subprocess.Popen(["/bin/true"]))
    blocked("unbound-read",lambda: open("/etc/hostname","rb"))
    blocked("outside-compile",lambda: compile(b"pass","<i178-outside-probe>","exec"))
    blocked("outside-exec",lambda: exec(outside_code,{}))
    blocked("forged-owned-source",lambda: compile(b"pass",str(OWN/"math178.py"),"exec"))
    ns = {"__name__":"i178_sealed_diagnostic"}
    for name in ("math178.py","research178.py"):
        path = str(OWN/name)
        code = compile(source[path],path,"exec")
        remember(code)
        exec(code,ns)
    def load(path):
        assert path in memory and path.endswith(".json")
        return json.loads(memory[path])
    comparisons = []
    for replay in inv["replays"]:
        began = time.perf_counter()
        result = encode(ns[replay["function"]](load))
        assert result == memory[replay["payload"]], replay["function"]
        comparisons.append({"function":replay["function"],"sha256":sha(result),
                            "byte_identical":True,"seconds":time.perf_counter()-began})
    for path,data in memory.items():
        assert (ROOT/path).read_bytes() == data, path
    for path,data in current_context.items():
        assert (ROOT/path).read_bytes() == data, path
    for path,data in control_memory.items():
        assert (ROOT/path).read_bytes() == data, path
    assert members() == before_members
    result = {"status":"PASS","iteration":178,"prevalidation":prevalidate,
              "owned":len(inv["owned"]),"external":len(inv["external"]),"contexts":4,
              "inventory_sha256":sha(invbytes),"report_sha256":sha(memory[REPORT]),
              "verifier_sha256":sha(memory[REL+"verify178.py"]),
              "seal_sha256":None if prevalidate else sha(control_memory[REL+"seal.json"]),
              "comparisons":comparisons,"probes":probes,
              "before_after":"Strict bytes, controls, membership and current context bytes unchanged",
              "context_current":{p:sha(b) for p,b in sorted(current_context.items())},
              "context_inherited":inv["context"],
              "runtime_seconds":time.perf_counter()-start,
              "limits":"Python audit guard only; OS sandbox and clean-clone reproduction not tested"}
    sys.stdout.buffer.write(encode(result))


if __name__ == "__main__":
    main()
