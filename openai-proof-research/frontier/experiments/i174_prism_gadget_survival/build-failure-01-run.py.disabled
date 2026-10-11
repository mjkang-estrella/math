"""Exclusive development receipts and exact source snapshots, including failures."""
from pathlib import Path
import hashlib
import json
import sys
import time
import traceback
import types

HERE = Path(__file__).resolve().parent


def install(name):
    module = types.ModuleType(name)
    path = HERE / (name+".py")
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(path.read_bytes(),str(path),"exec"),module.__dict__)
    return module


auth = install("authenticate")
memory, receipt = auth.authenticate()
kit = install("mathkit")
research = install("research")
name = sys.argv[1]
number = 1
while (HERE / f"{name}-attempt-{number:02d}.json").exists():
    number += 1
stem = f"{name}-attempt-{number:02d}"
for module in ("authenticate","mathkit","research","run"):
    with (HERE / f"{stem}-{module}.py.disabled").open("xb") as f:
        f.write((HERE / (module+".py")).read_bytes())
start = time.monotonic()
with (HERE / (stem+".json")).open("x") as out, (HERE / (stem+"-error.txt")).open("x") as err:
    try:
        if name != "mandatory":
            research.mandatory(memory)
        result = getattr(research,name)(memory)
        json.dump(result,out,sort_keys=True,indent=2)
        out.write("\n")
        status = "PASS"
    except BaseException:
        traceback.print_exc(file=err)
        status = "FAIL"
elapsed = time.monotonic()-start
receipt = dict(function=name,attempt=number,status=status,runtime_seconds=elapsed,
               source_snapshots=True,payload=stem+".json")
with (HERE / (stem+"-receipt.json")).open("x") as f:
    json.dump(receipt,f,indent=2,sort_keys=True)
    f.write("\n")
print(json.dumps(receipt))
sys.exit(0 if status == "PASS" else 1)
