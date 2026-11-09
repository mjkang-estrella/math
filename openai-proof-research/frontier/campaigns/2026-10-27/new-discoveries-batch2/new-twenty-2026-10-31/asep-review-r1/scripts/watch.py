#!/usr/bin/env python3
"""RSS/CPU/wall watchdog (reviewer's own).
usage: watch.py LOG.json -- cmd args...
Runs cmd in its own session pinned to 2 CPUs with RLIMIT_CPU=120 s, MALLOC_ARENA_MAX=2; samples the
private RSS (Private_Clean+Private_Dirty from smaps_rollup) and total RSS of the whole process tree every
0.1 s; kills the tree if private RSS > 6 GiB or wall > 140 s. Writes a JSON receipt."""
import os, sys, time, json, signal, subprocess, resource
LIM_PRIV = 6 * 1024**3; WALL = 140; CPU = 120
log = sys.argv[1]; cmd = sys.argv[sys.argv.index("--") + 1:]
def pre():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_CPU, (CPU, CPU + 2))
    os.sched_setaffinity(0, {0, 1})
env = dict(os.environ, MALLOC_ARENA_MAX="2")
t0 = time.time()
p = subprocess.Popen(cmd, preexec_fn=pre, env=env)
def tree(root):
    kids = {}
    for d in os.listdir("/proc"):
        if d.isdigit():
            try:
                with open(f"/proc/{d}/stat") as f: s = f.read()
                pp = int(s[s.rindex(")") + 2:].split()[1]); kids.setdefault(pp, []).append(int(d))
            except Exception: pass
    out, st = [], [root]
    while st:
        x = st.pop(); out.append(x); st += kids.get(x, [])
    return out
def mem(pid):
    priv = rss = 0
    try:
        with open(f"/proc/{pid}/smaps_rollup") as f:
            for l in f:
                if l.startswith(("Private_Clean:", "Private_Dirty:")): priv += int(l.split()[1]) * 1024
                elif l.startswith("Rss:"): rss += int(l.split()[1]) * 1024
    except Exception: pass
    return priv, rss
peak_priv = peak_rss = 0; killed = None
while p.poll() is None:
    pr = rs = 0
    for q in tree(p.pid):
        a, b = mem(q); pr += a; rs += b
    peak_priv = max(peak_priv, pr); peak_rss = max(peak_rss, rs)
    if pr > LIM_PRIV: killed = "private_rss"
    elif time.time() - t0 > WALL: killed = "wall"
    if killed:
        try: os.killpg(p.pid, signal.SIGKILL)
        except Exception: pass
        p.wait(); break
    time.sleep(0.1)
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
rec = {"cmd": cmd, "rc": p.returncode, "wall_s": round(time.time() - t0, 2), "cpu_s": round(ru.ru_utime + ru.ru_stime, 2),
       "peak_private_rss_MiB": peak_priv // 2**20, "peak_total_rss_MiB": peak_rss // 2**20,
       "maxrss_MiB_rusage": ru.ru_maxrss // 1024, "killed": killed, "utc_end": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
json.dump(rec, open(log, "w"), indent=1)
print(json.dumps(rec), file=sys.stderr)
sys.exit(p.returncode if p.returncode is not None else 1)
