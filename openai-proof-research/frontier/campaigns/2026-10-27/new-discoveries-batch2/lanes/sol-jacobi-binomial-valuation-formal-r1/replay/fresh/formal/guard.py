#!/usr/bin/env python3
import sys, subprocess, time, json, os, signal
from pathlib import Path
cmd=sys.argv[1:]; start=time.time(); peak=0; fired=False
p=subprocess.Popen(cmd)
while p.poll() is None:
    try:
        ids=[p.pid]
        children=Path(f'/proc/{p.pid}/task/{p.pid}/children')
        if children.exists(): ids += [int(x) for x in children.read_text().split()]
        rss=0
        for i in ids:
            status=Path(f'/proc/{i}/status')
            if status.exists(): rss += sum(int(x.split()[1]) for x in status.read_text().splitlines() if x.startswith('VmRSS:'))
        peak=max(peak,rss)
        if rss>3*1024*1024:
            fired=True
            for i in ids[::-1]:
                try: os.kill(i,signal.SIGKILL)
                except ProcessLookupError: pass
            break
    except FileNotFoundError: pass
    time.sleep(.1)
rc=p.wait()
print(json.dumps({'command':cmd,'exit_code':rc,'peak_rss_kib':peak,'rss_limit_kib':3*1024*1024,'guard_fired':fired,'elapsed_seconds':time.time()-start}))
sys.exit(rc if not fired else 137)
