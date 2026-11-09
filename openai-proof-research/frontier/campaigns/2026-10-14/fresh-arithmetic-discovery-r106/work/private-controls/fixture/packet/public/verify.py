"""Read-only packet verifier. Original code, MIT; not a mathematical gate."""
import argparse,hashlib,json,os,re,stat
from pathlib import Path

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def regular(p):
    s=p.lstat();need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'not a single-link regular file: '+str(p));return s
def inside(base,s):
    p=Path(s);need(not p.is_absolute() and '..' not in p.parts,'unsafe path');return base/p

def verify(a):
    root=Path(a.root);need(not root.is_symlink(),'root symlink');packet=root/'packet';need(not packet.is_symlink(),'packet symlink')
    for value in (a.final_sha256,a.manifest_sha256,a.report_sha256):need(bool(re.fullmatch('[0-9a-f]{64}',value)),'bad detached hash')
    for p,h in [(packet/'FINAL.json',a.final_sha256),(packet/'MANIFEST.json',a.manifest_sha256),(root/'REPORT.md',a.report_sha256)]:
        regular(p);need(digest(p)==h,'detached anchor mismatch: '+p.name)
    final=json.loads((packet/'FINAL.json').read_text());need(final['manifest_sha256']==a.manifest_sha256 and final['report_sha256']==a.report_sha256,'final bindings')
    m=json.loads((packet/'MANIFEST.json').read_text());actual_files={};actual_dirs={}
    for here,ds,fs in os.walk(packet,followlinks=False):
        for d in ds:
            p=Path(here)/d;s=p.lstat();need(stat.S_ISDIR(s.st_mode),'non-directory/symlink: '+str(p));actual_dirs[str(p.relative_to(packet))]=stat.S_IMODE(s.st_mode)
        for f in fs:
            p=Path(here)/f;s=regular(p);rel=str(p.relative_to(packet))
            if rel in ('FINAL.json','MANIFEST.json'):continue
            actual_files[rel]={'sha256':digest(p),'size':s.st_size,'mode':stat.S_IMODE(s.st_mode)}
    need(actual_files==m['files'],'payload inventory/hash/mode mismatch');need(actual_dirs==m['directories'],'directory inventory/mode mismatch')
    bindings=json.loads((packet/'private/original-bindings.json').read_text());project=Path(a.original_project)
    for e in bindings:
        p=inside(packet,e['copy']);need(digest(p)==e['sha256'] and p.stat().st_size==e['size'],'captured original mismatch')
        original=inside(project,e['original']);need(not original.is_symlink() and digest(original)==e['sha256'],'current original changed: '+e['original'])
    tree_entry=next(e for e in bindings if e['original']=='sources/preprints-tree.json');tree_path=inside(packet,tree_entry['copy'])
    need(digest(tree_path)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','tree anchor')
    tree=json.loads(tree_path.read_text());need(tree.get('truncated') is False and len(tree['tree'])==13223,'tree extent');idx={e['path']:e for e in tree['tree']}
    receipts=json.loads((packet/'private/source-receipts.json').read_text())
    pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    for e in receipts:
        p=inside(packet/'private/upstream',e['path']);b=p.read_bytes();t=idx[e['path']]
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        need(len(b)==e['size']==t['size'] and blob==e['git_blob']==t['sha'] and digest(p)==e['sha256'],'source identity')
        need(e['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path'],'source URL')
    primary=json.loads((packet/'private/primary/receipts.json').read_text())
    for e in primary:
        p=inside(packet/'private/primary',e['name']+'.pdf');need(p.stat().st_size==e['size'] and digest(p)==e['sha256'],'primary identity')
    return {'artifact_only':True,'status':'verified','payloads':len(actual_files),'directories':len(actual_dirs),'current_originals':len(bindings),'pinned_blobs':len(receipts),'primary_pdfs':len(primary)}
def parser():
    p=argparse.ArgumentParser()
    for n in ('root','final-sha256','manifest-sha256','report-sha256','original-project'):p.add_argument('--'+n,required=True)
    return p
if __name__=='__main__':
    try:print(json.dumps(verify(parser().parse_args()),sort_keys=True))
    except Exception as e:raise SystemExit('VERIFICATION FAILED: '+str(e))
