import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
from pathlib import Path
import sys
lane=Path(__file__).resolve().parent
rel=Path(sys.argv[1]); assert not rel.is_absolute() and '..' not in rel.parts
out=(lane/rel).resolve(); assert out.is_relative_to(lane)
out.parent.mkdir(parents=True,exist_ok=True); out.write_text(sys.stdin.read())
