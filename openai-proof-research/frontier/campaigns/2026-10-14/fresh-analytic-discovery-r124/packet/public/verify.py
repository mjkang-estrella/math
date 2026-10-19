#!/usr/bin/env python3
"""Read-only identity verifier; not a mathematical or contribution gate."""
import argparse, hashlib, json, os, pathlib, re, stat, sys
sys.dont_write_bytecode = True

def audit(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise PermissionError('DENIED write')
    if event.startswith(('subprocess.', 'socket.')) or event in {'os.system','os.fork','os.posix_spawn','os.exec','os.spawn','os.remove','os.rmdir','os.mkdir','os.rename','os.link','os.symlink','os.chmod','os.chown','os.truncate','os.utime','shutil.copyfile'}:
        raise PermissionError('DENIED mutation/process/network')
sys.addaudithook(audit)

def require(ok, why):
    if not ok: raise ValueError(why)
def digest(data): return hashlib.sha256(data).hexdigest()
def regular(p):
    s=p.lstat(); require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'not singly linked regular file: '+str(p)); return s
def read(p): regular(p); return p.read_bytes()
def pairs(items):
    d={}
    for k,v in items:
        require(k not in d,'duplicate JSON key'); d[k]=v
    return d
def obj(p): return json.loads(read(p), object_pairs_hook=pairs)
def rel(root, name):
    require(isinstance(name,str) and bool(name) and '\\' not in name, 'invalid path')
    p=pathlib.PurePosixPath(name)
    require(not p.is_absolute() and all(x not in ('','..','.') for x in name.split('/')), 'unsafe path')
    return root.joinpath(*p.parts)
def record(p):
    s=regular(p);return {'bytes':s.st_size,'sha256':digest(read(p)),'mode':stat.S_IMODE(s.st_mode)}
def inventory(root):
    files={};dirs={}
    def walk(p,name):
        s=p.lstat();require(stat.S_ISDIR(s.st_mode),'not directory: '+str(p));dirs[name]=stat.S_IMODE(s.st_mode)
        for q in sorted(p.iterdir()):
            n=q.name if name=='.' else name+'/'+q.name;s=q.lstat()
            if stat.S_ISDIR(s.st_mode):walk(q,n)
            else:files[n]=record(q)
    walk(root,'.');return {'files':files,'directories':dirs}
def check_binding(packet, item, key='local', hashkey='sha256'):
    p=rel(packet,item[key]);data=read(p); require(digest(data)==item[hashkey],'evidence binding '+item[key])
    if 'bytes' in item:require(len(data)==item['bytes'],'evidence size')
    return data

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);ap.add_argument('--tree',required=True)
    a=ap.parse_args()
    for h in (a.finalhash,a.reporthash):require(bool(re.fullmatch('[0-9a-f]{64}',h)),'invalid detached hash')
    root=pathlib.Path(a.root).absolute(); require(stat.S_ISDIR(root.lstat().st_mode),'root directory')
    finalbytes=read(root/'FINAL.json');require(digest(finalbytes)==a.finalhash,'DETACHED FINAL mismatch'); f=obj(root/'FINAL.json')
    require(f['status']=='PREFREEZE_NO_NOMINEE' and f['frozen_target'] is None,'scope status')
    require(f['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin')
    require(record(root/'REPORT.md')==f['outside_report'],'outside report binding')
    require(f['outside_report']['sha256']==a.reporthash,'DETACHED REPORT mismatch')
    require(record(root/'MANIFEST.json')==f['manifest'],'manifest binding')
    packet=root/'packet';m=obj(root/'MANIFEST.json')
    require(inventory(packet)==m,'exact packet inventory/bytes/modes mismatch')
    require(record(packet/'public/report.md')==f['public_report'],'public report binding')
    require(pathlib.Path(__file__).absolute()==packet/'public/verify.py','execute own packet verifier')
    treebytes=read(pathlib.Path(a.tree));require(digest(treebytes)==f['tree_sha256'],'external complete tree hash')
    tree=json.loads(treebytes,object_pairs_hook=pairs)
    require(tree['truncated'] is False and len(tree['tree'])==13223,'complete tree shape')
    entries={x['path']:x for x in tree['tree']};require(len(entries)==13223,'tree path uniqueness')
    require(sum(x['type']=='blob' for x in entries.values())==10373,'tree blob count')
    retained=obj(packet/'public/canonical.json');removed=obj(packet/'public/removed-acquisitions.json');seen=set()
    for x in retained+removed:
        require(x['path'] not in seen,'duplicate canonical path');seen.add(x['path'])
        require(entries[x['path']]==x['tree_entry'],'FULL canonical record')
        e=entries[x['path']];require(e['type']==x['type']=='blob' and e['sha']==x['blob'] and e['size']==x['size'],'canonical fields')
        require(x['url']=='https://raw.githubusercontent.com/openai/math/'+f['pin']+'/'+x['path'],'pinned raw URL')
        if x in retained:
            b=check_binding(packet,x);require(len(b)==x['size'],'canonical size')
            require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['blob'],'Git blob')
            require(re.findall(r'\\label\{([^}]+)\}',b.decode())==x['labels_present_not_read_claim'],'label inventory')
        else: require(not rel(packet,x['local']).exists(),'removed body unexpectedly retained')
    prim=obj(packet/'public/primary.json')
    for x in prim:
        check_binding(packet,x,'pdf','pdf_sha256');check_binding(packet,x,'text','text_sha256')
    for registry in ['history-register.json','context-register.json']:
        for x in obj(packet/'public'/registry):check_binding(packet,x)
    s=obj(packet/'public/search-register.json');check_binding(packet,{'local':s['hits_local'],'sha256':s['hits_sha256']})
    require(s['exit']==0 and s['no_size_cutoff'] and s['work_scratch_included'],'search receipt')
    return {'status':'IDENTITY_ONLY_OK','files':len(m['files']),'directories_including_root':len(m['directories']),'canonical':len(retained),'removed_acquisitions':len(removed),'primary_pairs':len(prim),'final_sha256':a.finalhash,'outside_report_sha256':a.reporthash}
if __name__=='__main__':
    try: print(json.dumps(main(),sort_keys=True))
    except Exception as e:
        print(json.dumps({'status':'REJECT','reason':str(e)}),file=sys.stderr);sys.exit(1)
