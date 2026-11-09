#!/usr/bin/env python3
"""Run one command under the review resource caps and write a receipt.
Usage: capped.py NAME [--cwd DIR] -- CMD...
Caps: systemd user scope MemoryMax=6G, 2 CPUs (taskset 0,1), RLIMIT_CPU 120 s,
wall 140 s, sampled private RSS of the whole process tree <= 6 GiB, MALLOC_ARENA_MAX=2.
Log: logs/NAME.log; receipt: receipts/run-NAME.json."""
import os, sys, subprocess, time, json, pathlib, signal, datetime
ROOT = pathlib.Path(__file__).resolve().parent.parent
args = sys.argv[1:]; name = args.pop(0); cwd = str(ROOT)
if args[0] == "--cwd": args.pop(0); cwd = args.pop(0)
assert args.pop(0) == "--"
cmd = args
env = dict(os.environ, MALLOC_ARENA_MAX="2", OMP_NUM_THREADS="2", OPENBLAS_NUM_THREADS="2",
           PYTHONDONTWRITEBYTECODE="1", TMPDIR=str(ROOT / "work" / "tmp"))
(ROOT / "work" / "tmp").mkdir(parents=True, exist_ok=True)
full = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0",
        "taskset", "-c", "0,1", "prlimit", "--cpu=120", "--"] + cmd
def tree(pid):
    out = [pid]; i = 0
    while i < len(out):
        try:
            kids = pathlib.Path(f"/proc/{out[i]}/task/{out[i]}/children").read_text().split()
            out += [int(k) for k in kids]
        except OSError: pass
        i += 1
    return out
def rss(pids):
    s = 0
    for p in pids:
        try:
            for l in pathlib.Path(f"/proc/{p}/smaps_rollup").read_text().splitlines():
                if l.startswith(("Private_Clean:", "Private_Dirty:", "Private_Hugetlb:")): s += int(l.split()[1]) * 1024
        except OSError: pass
    return s
t0 = time.monotonic(); start = datetime.datetime.now(datetime.timezone.utc).isoformat(); peak = 0; reason = None
with (ROOT / "logs" / (name + ".log")).open("w") as out:
    p = subprocess.Popen(full, stdout=out, stderr=subprocess.STDOUT, env=env, cwd=cwd, start_new_session=True)
    while p.poll() is None:
        peak = max(peak, rss(tree(p.pid)))
        if peak > 6 * 1024**3: reason = "private RSS cap"
        if time.monotonic() - t0 > 140: reason = "wall cap"
        if reason:
            os.killpg(p.pid, signal.SIGKILL); break
        time.sleep(0.1)
    code = p.wait()
r = dict(name=name, command=cmd, cwd=cwd, start_utc=start, returncode=code, wall_seconds=round(time.monotonic() - t0, 3),
         sampled_private_rss_peak_bytes=peak, killed_reason=reason, caps=dict(cpu_seconds=120, wall_seconds=140, cpus="0,1",
         memory_max="6G systemd user scope", private_rss_GiB=6, malloc_arena_max=2))
(ROOT / "receipts" / ("run-" + name + ".json")).write_text(json.dumps(r, indent=1) + "\n")
print(json.dumps(r)); print((ROOT / "logs" / (name + ".log")).read_text()[-3000:])
sys.exit(0 if code == 0 and reason is None else 1)
