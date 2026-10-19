#!/usr/bin/env python3
"""Read-only byte/provenance authentication. NOT a mathematical gate."""
import argparse,hashlib,json,os,pathlib,re,stat,sys
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREEHASH='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
SCOPEHASH='ec09396badbea0351a0eb2f8bdb7b780e1d74ffdace92bb04114cccdc5be4a22'
def guard(event,args):
    if event=='open':
        mode=args[1];flags=args[2]
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('AUDIT_DENIED_WRITE')
    if event.startswith(('subprocess.','socket.')) or event in {'os.system','os.exec','os.posix_spawn','os.fork','os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.link','os.symlink','os.truncate','os.utime'}:
        raise PermissionError('AUDIT_DENIED_OPERATION:'+event)
sys.addaudithook(guard)
def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def reg(p):
    s=p.lstat();need(stat.S_ISREG(s.st_mode),'not regular:'+str(p));need(s.st_nlink==1,'hardlink:'+str(p));need(s.st_mode & 0o444,'read denied mode:'+str(p));return s

def data(p):reg(p);return p.read_bytes()
def safe(s):
    need(isinstance(s,str) and s and '\\' not in s,'bad relative path')
    p=pathlib.PurePosixPath(s);need(not p.is_absolute() and all(x not in ('','.','..') for x in s.split('/')),'unsafe path:'+s);return p

def inventory(root):
    files={};dirs={}
    def walk(p,rel):
        s=p.lstat();need(stat.S_ISDIR(s.st_mode),'not directory:'+str(p));need(s.st_mode&0o444 and s.st_mode&0o111,'directory access denied:'+str(p));dirs[rel]=stat.S_IMODE(s.st_mode)
        for c in sorted(p.iterdir()):
            key=c.relative_to(root).as_posix();s=c.lstat()
            if stat.S_ISDIR(s.st_mode):walk(c,key)
            else:
                reg(c);files[key]={'sha256':sha(c.read_bytes()),'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode)}
    walk(root,'.');return files,dirs

def check(root,fh,rh):
    need(re.fullmatch('[0-9a-f]{64}',fh) and re.fullmatch('[0-9a-f]{64}',rh),'detached hash syntax')
    need(stat.S_ISDIR(root.lstat().st_mode),'root not directory')
    fb=data(root/'FINAL.json');need(sha(fb)==fh,'detached FINAL hash mismatch');f=json.loads(fb)
    rb=data(root/'REPORT.md');need(sha(rb)==rh==f['report_sha256'],'detached REPORT mismatch')
    need(f['pin']==PIN,'pin mismatch');packet=root/'packet';mb=data(packet/'MANIFEST.json');need(sha(mb)==f['manifest_sha256'],'manifest hash mismatch')
    need(stat.S_IMODE((packet/'MANIFEST.json').lstat().st_mode)==f['manifest_mode'],'manifest mode mismatch')
    m=json.loads(mb);need(m['version']==1,'manifest version');files,dirs=inventory(packet)
    need('MANIFEST.json' not in m['files'],'manifest self member')
    for k in m['files']:safe(k)
    for k in m['directories']:
        if k!='.':safe(k)
    need(set(files)==set(m['files'])|{'MANIFEST.json'},'exact file membership mismatch')
    need(dirs==m['directories'],'exact directory membership/mode mismatch')
    for k,v in m['files'].items():need(files[k]==v,'payload mismatch:'+k)
    for k,v in f['payload_anchors'].items():safe(k);need(files[k]['sha256']==v,'anchor mismatch:'+k)
    need(files['public/FROZEN-SCOPE.md']['sha256']==SCOPEHASH,'frozen scope changed')
    fr=json.loads(data(packet/'private/freeze.json'));need(fr['scope_sha256']==SCOPEHASH,'freeze record mismatch');need(fr['prefreeze_sha256']==files['public/prefreeze.md']['sha256'],'prefreeze mismatch')
    ctx=json.loads(data(packet/'private/context-register.json'));his=json.loads(data(packet/'private/history-register.json'))
    for r in ctx+his:
        safe(r['local']);b=data(packet/r['local']);need(len(b)==r['bytes'] and sha(b)==r['sha256'],'copied evidence mismatch')
    trees=[r for r in ctx if r['origin']=='sources/preprints-tree.json'];need(len(trees)==1,'tree count');tb=data(packet/trees[0]['local']);need(sha(tb)==TREEHASH,'canonical tree hash')
    t=json.loads(tb);need(t['truncated'] is False and len(t['tree'])==13223,'complete tree contract');by={x['path']:x for x in t['tree']};need(len(by)==13223,'tree duplicate')
    a=json.loads(data(packet/'private/upstream-register.json'));seen=set();kept=0
    for r in a:
        c=r['canonical'];p=c['path'];need(p not in seen,'duplicate canonical');seen.add(p);need(c==by[p],'FULL canonical record mismatch');need(c['type']=='blob','canonical type');need(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p,'pinned raw URL')
        safe(r['local']);need(r['local']=='private/upstream/'+p,'source placement')
        if r['retained']:
            b=data(packet/r['local']);need(len(b)==c['size'] and sha(b)==r['sha256'],'source sha/size');need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==c['sha'],'Git blob mismatch');need(re.findall(r'\\label\{([^}]+)\}',b.decode())==r['labels_present'],'label inventory');kept+=1
        else:need(not (packet/r['local']).exists(),'removed body unexpectedly present')
    pr=json.loads(data(packet/'private/primary/register.json'));success=0;failure=0
    for r in pr:
        if 'error' in r:failure+=1;continue
        name=r['name'];safe(name);b=data(packet/('private/primary/'+name+'.pdf'));x=data(packet/('private/primary/'+name+'.txt'));need(b.startswith(b'%PDF') and len(b)==r['bytes'] and sha(b)==r['sha256'] and sha(x)==r['text_sha256'] and r['extraction_returncode']==0,'primary pair mismatch:'+name);success+=1
    return {'status':'ARTIFACTS_AUTHENTICATED_ONLY','payload_files':len(m['files']),'directories_including_root':len(dirs),'canonical_records':len(a),'retained_sources':kept,'primary_pairs':success,'failed_primary_requests':failure,'frozen_scope_sha256':SCOPEHASH,'mathematical_gate':False,'contribution_gate':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=pathlib.Path,required=True);p.add_argument('--finalhash',required=True);p.add_argument('--reporthash',required=True);a=p.parse_args()
    try:print(json.dumps(check(a.root,a.finalhash,a.reporthash),sort_keys=True))
    except Exception as e:print(json.dumps({'status':'REJECT','reason':str(e)},sort_keys=True));return 1
    return 0
if __name__=='__main__':sys.exit(main())
