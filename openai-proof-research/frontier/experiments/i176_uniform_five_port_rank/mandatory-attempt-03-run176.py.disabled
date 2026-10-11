"""Development runner: preserves every source stage, stdout and stderr."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = sys.argv[1]
attempt = sys.argv[2]
prefix = HERE / (name + "-attempt-" + attempt)
assert not Path(str(prefix)+".json").exists()
for filename in ["math176.py", "research176.py", "run176.py"]:
    with Path(str(prefix)+"-"+filename+".disabled").open("xb") as f:
        f.write((HERE/filename).read_bytes())
namespace = {"__name__":"math176"}
exec(compile((HERE/"math176.py").read_bytes(),str(HERE/"math176.py"),"exec"),namespace)
research = {"M":type("Math",(),namespace), "READ":lambda p:(ROOT/p).read_bytes()}
exec(compile((HERE/"research176.py").read_bytes(),str(HERE/"research176.py"),"exec"),research)
start = time.monotonic()
out,err = io.StringIO(),io.StringIO()
status = "PASS"
try:
    with contextlib.redirect_stderr(err):
        result = research[name]()
    out.write(json.dumps(result,sort_keys=True,indent=2)+"\n")
except BaseException:
    status = "FAIL"
    traceback.print_exc(file=err)
for suffix,value in [(".json",out.getvalue()),("-stderr.txt",err.getvalue())]:
    with Path(str(prefix)+suffix).open("x") as f:
        f.write(value)
receipt = {"status":status,"seconds":time.monotonic()-start,
           "stdout_sha256":hashlib.sha256(out.getvalue().encode()).hexdigest(),
           "stderr_empty":not err.getvalue()}
with Path(str(prefix)+"-receipt.json").open("x") as f:
    json.dump(receipt,f,indent=2,sort_keys=True)
    f.write("\n")
print(json.dumps(receipt))
if status != "PASS":
    print(err.getvalue(),file=sys.stderr)
    sys.exit(1)
