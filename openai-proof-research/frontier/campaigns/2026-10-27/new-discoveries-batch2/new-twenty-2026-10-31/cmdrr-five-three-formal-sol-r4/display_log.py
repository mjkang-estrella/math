import os, resource
os.sched_setaffinity(0, set(sorted(os.sched_getaffinity(0))[:2]))
resource.setrlimit(resource.RLIMIT_CPU, (10,10))
resource.setrlimit(resource.RLIMIT_AS, (536870912,536870912))
from pathlib import Path
import sys, hashlib, json, time, subprocess
root = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4/logs")
p = Path(sys.argv[1])
assert p.is_absolute() and p.resolve().is_relative_to(root)
offset = int(sys.argv[2])
assert offset >= 0
h = hashlib.sha256()
with p.open("rb") as f:
    for b in iter(lambda: f.read(65536), b""):
        h.update(b)
if len(sys.argv)>3:
    assert h.hexdigest() == sys.argv[3]
with p.open("rb") as f:
    f.seek(offset)
    data = f.read(16384)
rec = dict(command=["timeout","20","python3","-I","-B",*sys.argv],offset=offset,
    bytes=len(data),log_sha256=h.hexdigest(),exit=0,affinity=sorted(os.sched_getaffinity(0)),
    cpu_limit=10,as_limit=536870912,under_compiler_runner=False,sampled_group_telemetry=None,
    native_UI_telemetry=None,authorization="Prospective root own-log display exception")
subprocess.run(["python3","-I","-B","/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4/write_lane.py",
    "audit/displays/"+str(time.time_ns())+".json"],input=json.dumps(rec,indent=1),text=True,check=True)
print("DISPLAY", str(p), "OFFSET", offset, "BYTES", len(data), "SHA256", h.hexdigest())
print(data.decode("utf-8", errors="replace"))
