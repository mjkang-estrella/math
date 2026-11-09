import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import pathlib,sys
lane=pathlib.Path(__file__).resolve().parent
rel=pathlib.PurePath(sys.argv[1])
assert not rel.is_absolute() and ".." not in rel.parts
target=(lane/rel).resolve()
assert target.is_relative_to(lane) and target!=lane and not target.is_symlink()
text=sys.stdin.read()
target.parent.mkdir(parents=True,exist_ok=True)
target.write_text(text)
print(str(target))
