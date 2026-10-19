#!/usr/bin/env python3
"""Read-only artifact verifier. Requires anchors supplied outside this packet."""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path
sys.dont_write_bytecode=True
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def readonly(event,args):
    if event=='open':
        mode,flags=args[1],args[2]
        if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('write denied')
    if event in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime','subprocess.Popen','os.system','socket.connect'}:
        raise RuntimeError('mutation/network denied')
sys.addaudithook(readonly)
def need(ok,message):
    if not ok: raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(root,name):
    p=Path(name)
    need(not p.is_absolute() and '..' not in p.parts and str(p)==name,'unsafe path')
    return root/p
def regular(p):
    s=p.lstat();need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'not single-link regular file: '+str(p));return s
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',required=True,type=Path)
    ap.add_argument('--tree',required=True,type=Path)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args();root=a.root.absolute();packet=root/'packet'
    for h in [a.final_sha256,a.report_sha256]:need(re.fullmatch('[0-9a-f]{64}',h) is not None,'invalid detached anchor')
    for n in ['FINAL.json','REPORT.md']:regular(root/n)
    need(sha(root/'FINAL.json')==a.final_sha256,'detached FINAL mismatch')
    need(sha(root/'REPORT.md')==a.report_sha256,'detached REPORT mismatch')
    f=json.loads((root/'FINAL.json').read_text())
    need(f['pin']==PIN and f['tree_sha256']==TREE,'fixed provenance mismatch')
    need(f['report_sha256']==a.report_sha256,'FINAL/REPORT binding')
    regular(packet/'MANIFEST.json')
    need(sha(packet/'MANIFEST.json')==f['manifest_sha256'],'manifest anchor')
    m=json.loads((packet/'MANIFEST.json').read_text())
    files={};dirs={}
    for base,ds,fs in os.walk(packet,followlinks=False):
        bp=Path(base);rel='.' if bp==packet else bp.relative_to(packet).as_posix()
        need(not bp.is_symlink(),'symlink directory')
        dirs[rel]=stat.S_IMODE(bp.lstat().st_mode)
        for d in ds:need(not (bp/d).is_symlink(),'symlink directory')
        for n in fs:
            p=bp/n;s=regular(p);k=p.relative_to(packet).as_posix()
            if k=='MANIFEST.json':continue
            files[k]={'sha256':sha(p),'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode)}
    need(files==m['files'],'exact payload bytes/size/mode set mismatch')
    need(dirs==m['directories'],'exact directory/mode set mismatch')
    need(sha(packet/'public/report.md')==f['public_report_sha256'],'public report binding')
    need(sha(packet/'code/verify.py')==f['verifier_sha256'],'verifier binding');need(sha(packet/'code/controls.py')==f['controls_sha256'],'controls binding')
    need(sha(a.tree)==TREE,'external complete tree digest')
    tree=json.loads(a.tree.read_text());need(tree['truncated'] is False and len(tree['tree'])==13223,'incomplete tree')
    index={x['path']:x for x in tree['tree']};need(len(index)==13223,'duplicate canonical paths')
    sources=json.loads((packet/'public/source-register.json').read_text());seen=set();retained=0
    for x in sources:
        c=x['canonical'];need(index.get(c['path'])==c,'full canonical record mismatch')
        need(c['type']=='blob','nonblob source')
        need(c['path'] not in seen,'duplicate source');seen.add(c['path'])
        need(x['raw_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+c['path'],'raw URL mismatch')
        p=safe(packet,x['local'])
        if x['retained']:
            b=p.read_bytes();need(len(b)==c['size'] and hashlib.sha256(b).hexdigest()==x['sha256'],'source body mismatch')
            need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==c['sha'],'Git blob mismatch');retained+=1
        else:need(not p.exists(),'removed source unexpectedly exists')
    primaries=json.loads((packet/'public/primary-register.json').read_text());pairs=0;failures=0
    for x in primaries:
        if 'error' in x:failures+=1;continue
        for k in ['pdf','text']:
            p=safe(packet,x[k])
            if x['retained']:need(sha(p)==x[k+'_sha256'],'primary mismatch')
            else:need(not p.exists(),'removed primary exists')
        pairs+=bool(x['retained'])
    context=json.loads((packet/'public/context-register.json').read_text())
    for x in context:
        p=safe(packet,x['local']);need(sha(p)==x['sha256'] and p.stat().st_size==x['bytes'],'context mismatch')
    renders=json.loads((packet/'private/render/register.json').read_text())
    for x in renders:need(sha(safe(packet,x['local']))==x['sha256'],'render mismatch')
    print(json.dumps({'artifact_verification':'PASS','payload_files':len(files),'directories_including_packet_root':len(dirs),'canonical_records':len(sources),'retained_canonical_bodies':retained,'runner':'Factory Droid Opus 5.5 high','retained_primary_pairs':pairs,'failed_primary_requests':failures,'context_history_copies':len(context),'renders':len(renders),'mathematical_gate':False},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
