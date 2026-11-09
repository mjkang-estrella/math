#!/usr/bin/env python3
"""Sequential Lean runner with a sampled 3 GiB RSS guard, no virtual-memory cap."""
import subprocess, sys, time, json, resource
from pathlib import Path
log = Path(sys.argv[1]); args=sys.argv[2:]
started=time.time(); peak=0; samples=0; killed=False
with log.open('w') as out:
    command=[sys.executable, 'run_lean.py', '-j1', '-M4096', '-DwarningAsError=true', '-DautoImplicit=false', *args]
    proc=subprocess.Popen(command, stdout=out, stderr=subprocess.STDOUT)
    while proc.poll() is None:
        # run_lean.py is parent of the actual Lean process.
        rss=0
        try:
            children=Path(f'/proc/{proc.pid}/task/{proc.pid}/children').read_text().split()
            for pid in [str(proc.pid), *children]:
                for line in Path(f'/proc/{pid}/status').read_text().splitlines():
                    if line.startswith('VmRSS:'): rss += int(line.split()[1])
        except (FileNotFoundError, ProcessLookupError): pass
        peak=max(peak,rss); samples+=1
        if rss > 3*1024*1024:
            killed=True
            for pid in children: subprocess.run(['kill','-KILL',pid], check=False)
            proc.kill()
        time.sleep(.2)
    code=proc.wait()
receipt={'command':command,'args':args,'sample_interval_seconds':0.2,'exit_code':code,'sampled_peak_rss_kib':peak,'samples':samples,'guard_kib':3*1024*1024,'guard_killed':killed,'seconds':time.time()-started}
log.with_suffix(log.suffix+'.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt)); print(log.read_text())
raise SystemExit(code)
