import os, resource, signal, subprocess, sys, time
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
os.sched_setaffinity(0, {0,1})
p = subprocess.Popen(sys.argv[1:], start_new_session=True)
start = time.monotonic()
while p.poll() is None:
    rss=0
    for pid in os.listdir('/proc'):
        if not pid.isdigit(): continue
        try:
            stat=open(f'/proc/{pid}/stat').read().rsplit(')',1)[1].split()
            if int(stat[3]) == p.pid:
                rss += int(open(f'/proc/{pid}/status').read().split('VmRSS:')[1].split()[0])
        except (FileNotFoundError, ProcessLookupError, PermissionError, IndexError):
            pass
    if rss > 6*1024*1024 or time.monotonic()-start > 140:
        os.killpg(p.pid, signal.SIGKILL)
        p.wait()
        sys.exit(124)
    time.sleep(.2)
sys.exit(p.returncode)
