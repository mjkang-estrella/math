"""Run a command with CPU/wall/address-space limits and an RSS watchdog (kills the process group above a cap).
usage: rsscap.py RSS_MB WALL_S CPU_S -- cmd args...
Prints a JSON line with exit status, peak RSS (MB, summed over the process tree) and elapsed time."""
import sys, os, time, json, signal, subprocess, resource
rss_mb, wall, cpu = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]); cmd = sys.argv[sys.argv.index('--') + 1:]
def lim():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
    resource.setrlimit(resource.RLIMIT_AS, (64 << 30, 64 << 30))
p = subprocess.Popen(cmd, preexec_fn=lim)
def tree_rss(pid):
    total = 0; stack = [pid]
    while stack:
        q = stack.pop()
        try:
            with open(f'/proc/{q}/statm') as f: total += int(f.read().split()[1]) * os.sysconf('SC_PAGE_SIZE')
            with open(f'/proc/{q}/task/{q}/children') as f: stack += [int(c) for c in f.read().split()]
        except OSError: pass
    return total >> 20
t0 = time.monotonic(); peak = 0; killed = None
while p.poll() is None:
    r = tree_rss(p.pid); peak = max(peak, r)
    if r > rss_mb: killed = 'rss'; os.killpg(p.pid, signal.SIGKILL); break
    if time.monotonic() - t0 > wall: killed = 'wall'; os.killpg(p.pid, signal.SIGKILL); break
    time.sleep(0.2)
p.wait()
print(json.dumps({'cmd': cmd[-1], 'exit': p.returncode, 'killed': killed, 'peak_rss_mb': peak, 'elapsed_s': round(time.monotonic() - t0, 2)}), file=sys.stderr)
sys.exit(p.returncode if p.returncode >= 0 else 1)
