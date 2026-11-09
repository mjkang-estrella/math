#!/usr/bin/env python3
"""Resource wrapper for cycramsey-review-r2.

Usage: python3 -I limited.py NAME LOGDIR -- CMD ARGS...

Runs CMD on CPUs 0,1 with RLIMIT_CPU 120 s, a wall limit of 140 s, MALLOC_ARENA_MAX=2,
and a sampled RSS cap (default 4 GiB) over the whole process tree (summed).  stdout and
stderr go to LOGDIR/NAME.log; a JSON receipt goes to LOGDIR/NAME.receipt.json.
"""
import json, os, resource, signal, subprocess, sys, time, datetime, hashlib

CPU_S = 120
WALL_S = 140
RSS_CAP = int(os.environ.get("RSS_CAP_BYTES", str(4 * 1024**3)))


def tree_rss(root):
    # Sum RSS over root and all descendants, via /proc.
    kids = {}
    for p in os.listdir("/proc"):
        if not p.isdigit():
            continue
        try:
            with open(f"/proc/{p}/stat") as f:
                s = f.read()
            ppid = int(s.rsplit(")", 1)[1].split()[1])
            kids.setdefault(ppid, []).append(int(p))
        except Exception:
            pass
    total, stack = 0, [root]
    while stack:
        q = stack.pop()
        try:
            with open(f"/proc/{q}/status") as f:
                for line in f:
                    if line.startswith("VmRSS:"):
                        total += int(line.split()[1]) * 1024
        except Exception:
            pass
        stack.extend(kids.get(q, []))
    return total


def main():
    name, logdir = sys.argv[1], sys.argv[2]
    assert sys.argv[3] == "--"
    cmd = sys.argv[4:]
    os.makedirs(logdir, exist_ok=True)
    log = os.path.join(logdir, name + ".log")
    env = dict(os.environ, MALLOC_ARENA_MAX="2")

    def pre():
        os.setsid()
        os.sched_setaffinity(0, {0, 1})
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_S, CPU_S))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    t0 = time.time()
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    peak, killed = 0, None
    with open(log, "wb") as out:
        p = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, env=env, preexec_fn=pre)
        while p.poll() is None:
            r = tree_rss(p.pid)
            peak = max(peak, r)
            if r > RSS_CAP:
                killed = "rss"
            elif time.time() - t0 > WALL_S:
                killed = "wall"
            if killed:
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                p.wait()
                break
            time.sleep(0.2)
    rc = p.returncode
    with open(log, "rb") as f:
        h = hashlib.sha256(f.read()).hexdigest()
    rec = {"name": name, "cmd": cmd, "cwd": os.getcwd(), "utc_start": start,
           "wall_s": round(time.time() - t0, 2), "rc": rc, "killed": killed,
           "peak_tree_rss_bytes": peak, "limits": {"cpus": [0, 1], "cpu_s": CPU_S,
           "wall_s": WALL_S, "rss_cap_bytes": RSS_CAP, "MALLOC_ARENA_MAX": 2},
           "log": log, "log_sha256": h}
    with open(os.path.join(logdir, name + ".receipt.json"), "w") as f:
        json.dump(rec, f, indent=1)
    print(f"{name}: rc={rc} killed={killed} wall={rec['wall_s']}s peakRSS={peak // 2**20}MiB")
    sys.exit(0 if rc == 0 and not killed else 1)


if __name__ == "__main__":
    main()
