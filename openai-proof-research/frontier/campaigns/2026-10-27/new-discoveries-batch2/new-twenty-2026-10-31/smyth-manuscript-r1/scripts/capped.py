import os,sys,resource,subprocess,time,json,signal
from pathlib import Path
root=Path(__file__).resolve().parent.parent
os.environ.update(MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',PYTHONDONTWRITEBYTECODE='1',TMPDIR=str(root/'tmp'))
(root/'tmp').mkdir(exist_ok=True)
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
label=sys.argv[1]; start=time.monotonic()
p=subprocess.Popen(sys.argv[2:],cwd=root,env=os.environ,start_new_session=True)
peak=0; reason=None
while p.poll() is None:
    rss=0
    for d in Path('/proc').iterdir():
        if not d.name.isdigit(): continue
        try:
            fields=(d/'stat').read_text().split()
            if int(fields[4])==p.pid:
                rss+=int(fields[23])*os.sysconf('SC_PAGE_SIZE')
        except (OSError,ValueError,IndexError): pass
    peak=max(peak,rss)
    if rss>=6*1024**3 or time.monotonic()-start>=138:
        reason='RSS or wall cap'; os.killpg(p.pid,signal.SIGKILL); break
    time.sleep(.1)
rc=p.wait()
(root/'receipts').mkdir(exist_ok=True)
(root/'receipts'/f'{label}.json').write_text(json.dumps(dict(command=sys.argv[2:],exit=rc,wall_seconds=time.monotonic()-start,sampled_peak_rss_bytes=peak,cpus=sorted(os.sched_getaffinity(0)),reason=reason),indent=2)+'\n')
sys.exit(rc)
