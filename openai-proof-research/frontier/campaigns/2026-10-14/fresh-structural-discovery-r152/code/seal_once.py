# Original code, MIT. One final seal; never overwrites an existing root manifest.
from pathlib import Path
import hashlib,json,os,stat
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r152')
assert Path.cwd()==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
if (ROOT/'MANIFEST.json').exists():raise SystemExit('Already sealed; refusing reseal')
outside={'FINAL.md','MANIFEST.json','REPORT.md'}
assert (ROOT/'FINAL.md').is_file() and (ROOT/'REPORT.md').is_file()
files={};dirs=['.']
def visit(base):
    for e in sorted(os.scandir(base),key=lambda e:e.name):
        p=Path(e.path);rel=p.relative_to(ROOT).as_posix();s=e.stat(follow_symlinks=False)
        if stat.S_ISLNK(s.st_mode):raise ValueError('symlink '+rel)
        if stat.S_ISDIR(s.st_mode):dirs.append(rel);visit(p)
        elif stat.S_ISREG(s.st_mode):
            assert s.st_nlink==1
            if rel not in outside:files[rel]={'size':s.st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
        else:raise ValueError('nonregular '+rel)
visit(ROOT)
m={'schema':'r152-exact-payload-v1','files':files,'directories':sorted(dirs)}
(ROOT/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({'root':str(ROOT),'payload_files':len(files),'directories':len(dirs),'anchors':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in sorted(outside)}},indent=2))
