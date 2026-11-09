import os, sys, subprocess, resource, time, signal
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
p = subprocess.Popen(sys.argv[1:])
while p.poll() is None:
    try:
        s=open(f"/proc/{p.pid}/status").read()
        rss=int(s.split("VmRSS:")[1].split()[0]) if "VmRSS:" in s else 0
        if rss>6291456: p.kill(); print("RSS limit exceeded",file=sys.stderr)
    except FileNotFoundError: pass
    time.sleep(.1)
sys.exit(p.returncode)
