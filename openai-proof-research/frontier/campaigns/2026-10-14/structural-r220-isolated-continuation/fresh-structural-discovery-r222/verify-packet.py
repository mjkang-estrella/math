"""Read-only verification of an exact local selection using detached explicit anchors."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat, sys

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def run():
    ap=argparse.ArgumentParser()
    for name in ['packet','manifest-sha256','final-sha256','report','report-sha256']:
        ap.add_argument('--'+name,required=True)
    a=ap.parse_args()
    own=Path(__file__).resolve().parent
    root=Path(a.packet).resolve(); report=Path(a.report).resolve()
    require(root.is_relative_to(own) and report.is_relative_to(own),'paths must stay in this exact own root')
    require(not Path(a.packet).is_symlink() and not Path(a.report).is_symlink(),'symlink input')
    manifest=root/'MANIFEST.json'
    require(digest(manifest)==a.manifest_sha256,'detached manifest anchor mismatch')
    require(digest(root/'FINAL.md')==a.final_sha256,'detached FINAL anchor mismatch')
    require(digest(report)==a.report_sha256,'detached REPORT anchor mismatch')
    require(stat.S_IMODE(manifest.stat().st_mode)==0o444,'manifest mode mismatch')
    require(stat.S_IMODE(report.stat().st_mode)==0o444,'report mode mismatch')
    data=json.loads(manifest.read_text())
    require(data['schema']=='r222-exact-selection-v1','manifest schema mismatch')
    wanted={}
    for row in data['files']:
        name=row['path']; p=PurePosixPath(name)
        require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==name,'unsafe path')
        require(name not in wanted and name!='MANIFEST.json','duplicate/self manifest entry')
        wanted[name]=row
    actual=set(); dirs={}
    def visit(p):
        rel=p.relative_to(root).as_posix()
        dirs['' if rel=='.' else rel]=format(stat.S_IMODE(p.stat().st_mode),'04o')
        with os.scandir(p) as entries:
            for ent in entries:
                q=Path(ent.path)
                require(not ent.is_symlink(),'symlink in packet')
                if ent.is_dir(follow_symlinks=False):visit(q)
                elif ent.is_file(follow_symlinks=False):actual.add(q.relative_to(root).as_posix())
                else:raise ValueError('nonregular packet entry')
    visit(root)
    require(actual==set(wanted)|{'MANIFEST.json'},'exact file selection mismatch')
    require(dirs==data['directories'],'exact directory selection/modes mismatch')
    for name,row in wanted.items():
        p=root/name
        require(p.stat().st_size==row['bytes'],'size mismatch: '+name)
        require(digest(p)==row['sha256'],'hash mismatch: '+name)
        require(format(stat.S_IMODE(p.stat().st_mode),'04o')==row['mode'],'mode mismatch: '+name)
    return {'ok':True,'files':len(wanted),'directories':len(dirs),'read_only':True,'mathematical_grade':None}

if __name__=='__main__':
    try:print(json.dumps(run(),sort_keys=True))
    except Exception as e:
        print(json.dumps({'ok':False,'error':str(e)},sort_keys=True));sys.exit(1)
