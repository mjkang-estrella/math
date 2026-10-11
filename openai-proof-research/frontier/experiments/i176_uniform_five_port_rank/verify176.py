"""Read-only I176 verifier. Authenticate memory before compiling owned code."""
import builtins
import contextlib
import fractions
import functools
import hashlib
import io
import itertools
import json
import math
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = "frontier/experiments/i176_uniform_five_port_rank/"
SOURCE = "frontier/sources/i176_uniform_five_port_rank/"
REPORT = "frontier/iterations/i176-uniform-five-port-rank.md"
PRE = "--prevalidate" in sys.argv
START = time.monotonic()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def owned_members():
    names = {REPORT}
    for prefix in (PREFIX, SOURCE):
        names.update(str(p.relative_to(ROOT)) for p in (ROOT/prefix).rglob("*") if p.is_file())
    return names


inv_bytes = (HERE/"inventory.json").read_bytes()
inventory = json.loads(inv_bytes)
control_paths = inventory["controls"]
assert len(control_paths)==3 and set(control_paths)=={
    PREFIX+"inventory.json",PREFIX+"prevalidation.json",PREFIX+"seal.json"}
controls = {p:(ROOT/p).read_bytes() for p in control_paths if (ROOT/p).exists()}
assert PRE == (PREFIX+"seal.json" not in controls)
if PRE:
    assert set(controls)=={PREFIX+"inventory.json"}
else:
    seal = json.loads(controls[PREFIX+"seal.json"])
    pre = json.loads(controls[PREFIX+"prevalidation.json"])
    assert seal["inventory_sha256"]==digest(inv_bytes)
    assert seal["prevalidation_sha256"]==digest(controls[PREFIX+"prevalidation.json"])
    assert pre["status"]=="PASS" and pre["prevalidation"]
    assert pre["stderr_empty"] and all(x["blocked"] for x in pre["probes"])
    assert seal["report_sha256"]==digest((ROOT/REPORT).read_bytes())
    assert seal["verifier_sha256"]==digest(Path(__file__).read_bytes())

bound = {}
for entry in inventory["owned"]+inventory["external"]:
    path = entry["path"]
    assert path not in bound
    data = (ROOT/path).read_bytes()
    assert len(data)==entry["size"] and digest(data)==entry["sha256"], path
    bound[path]=data
for path,data in controls.items():
    assert path not in bound
    bound[path]=data
context_before = {}
for entry in inventory["context"]:
    path=entry["path"]
    assert path not in bound
    data=(ROOT/path).read_bytes()
    context_before[path]=digest(data)
    # Deliberately no equality assertion against any historical context hash.
    bound[path]=data
MEMORY=types.MappingProxyType(bound)
del bound
before_members=owned_members()
assert before_members=={e["path"] for e in inventory["owned"]}|set(controls)

# Independently retain full I175 owned-set membership, without ancestor execution.
ancestor_inventory=json.loads(MEMORY["frontier/experiments/i175_affected_prism_exterior/inventory.json"])
ancestor_members={"frontier/iterations/i175-affected-prism-exterior.md"}
for prefix in ("frontier/experiments/i175_affected_prism_exterior/",
               "frontier/sources/i175_affected_prism_exterior/"):
    ancestor_members.update(str(p.relative_to(ROOT)) for p in (ROOT/prefix).rglob("*") if p.is_file())
assert ancestor_members=={e["path"] for e in ancestor_inventory["owned"]}|set(ancestor_inventory["controls"])

allowed_sources={str(ROOT/(PREFIX+name)):MEMORY[PREFIX+name]
                 for name in ("math176.py","research176.py","authenticate176.py")}
absolute_reads={str(ROOT/p) for p in MEMORY}
allowed_code=set()
foreign_code=compile("pass","<outside-I176>","exec")
original_compile=builtins.compile
original_exec=builtins.exec
compiled_source_event=None


class Blocked(PermissionError):
    pass


def audit(event,args):
    if event=="open":
        path,mode,flags=args
        if (isinstance(mode,str) and any(x in mode for x in "wax+")) or (
                isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise Blocked("write")
        if not isinstance(path,(str,bytes,os.PathLike)):
            raise Blocked("unbound fd")
        name=os.path.abspath(os.fsdecode(path))
        if name not in absolute_reads:
            raise Blocked("unbound read")
    elif event.startswith(("socket.","subprocess.","ctypes.")) or event in (
            "os.system","os.fork","os.forkpty","os.posix_spawn","os.exec","os.spawn"):
        raise Blocked("network/process")
    elif event in ("os.remove","os.rename","os.rmdir","os.mkdir","os.link","os.symlink",
                   "os.chmod","os.chown","os.truncate","os.utime","os.putenv","os.unsetenv"):
        raise Blocked("mutation")
    elif event=="compile":
        source,filename=args
        if isinstance(source,str):
            source=source.encode()
        if filename not in allowed_sources or source!=allowed_sources[filename]:
            raise Blocked("unowned or forged compilation")
    elif event=="exec" and args[0] not in allowed_code:
        raise Blocked("outside execution")


sys.addaudithook(audit)
probes=[]


def probe(name,action):
    try:
        action()
    except (Blocked,KeyError):
        probes.append({"probe":name,"blocked":True})
    else:
        raise AssertionError("probe escaped: "+name)


probe("write",lambda:open(str(HERE/"__blocked_write__"),"w"))
probe("mutation",lambda:os.mkdir(str(HERE/"__blocked_mutation__")))
probe("network",lambda:socket.socket())
probe("subprocess",lambda:subprocess.Popen(["__I176_NONEXISTENT_PROGRAM__"]))
probe("unbound-read",lambda:open(str(ROOT/"__I176_UNBOUND_READ__"),"rb"))
probe("outside-compile",lambda:original_compile("pass","<outside-I176>","exec"))
probe("outside-exec",lambda:original_exec(foreign_code,{}))
probe("forged-owned-source",lambda:original_compile(b"pass",str(HERE/"math176.py"),"exec"))


def load_owned(name,namespace):
    filename=str(HERE/name)
    code=original_compile(allowed_sources[filename],filename,"exec")
    allowed_code.add(code)
    original_exec(code,namespace)
    return namespace


auth=load_owned("authenticate176.py",{"__name__":"authenticate176","__file__":str(HERE/"authenticate176.py")})
auth_result=auth["authenticate"](MEMORY.__getitem__)
math_namespace=load_owned("math176.py",{"__name__":"math176"})
research=load_owned("research176.py",{"__name__":"research176","M":types.SimpleNamespace(**math_namespace),
                                    "READ":MEMORY.__getitem__})
comparisons=[]
captured_stderr=io.StringIO()
with contextlib.redirect_stderr(captured_stderr):
    for replay in inventory["replays"]:
        start=time.monotonic()
        value=research[replay["function"]]()
        result=(json.dumps(value,sort_keys=True,indent=2)+"\n").encode()
        assert result==MEMORY[replay["payload"]], replay["function"]
        comparisons.append({"function":replay["function"],"byte_identical":True,
                            "sha256":digest(result),"seconds":time.monotonic()-start})
assert not captured_stderr.getvalue()
for path,data in MEMORY.items():
    assert (ROOT/path).read_bytes()==data, path
assert owned_members()==before_members
context_after={p:digest((ROOT/p).read_bytes()) for p in context_before}
assert context_after==context_before
assert all(digest((ROOT/p).read_bytes())==digest(data) for p,data in controls.items())
result={"iteration":176,"status":"PASS","prevalidation":PRE,"stderr_empty":True,
        "owned":len(inventory["owned"]),"external":len(inventory["external"]),
        "contexts":len(inventory["context"]),"comparisons":comparisons,"probes":probes,
        "before_after":"all mathematical bytes, controls, complete owned membership and current context bytes unchanged",
        "context_before":context_before,"context_after":context_after,
        "inherited_context_drift":[p for p in auth_result["contexts"] if p["drift"]],
        "runtime_seconds":time.monotonic()-START,"inventory_sha256":digest(inv_bytes),
        "report_sha256":digest(MEMORY[REPORT]),"verifier_sha256":digest(MEMORY[PREFIX+"verify176.py"]),
        "seal_sha256":None if PRE else digest(controls[PREFIX+"seal.json"]),
        "limits":"Python audit guard, not OS sandbox; no clean-clone reconstruction; no ancestor execution"}
print(json.dumps(result,sort_keys=True,indent=2))
