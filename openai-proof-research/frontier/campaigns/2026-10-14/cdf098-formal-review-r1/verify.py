#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Read-only externally anchored scoped formal audit inventory. Identity only."""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path,PurePosixPath
SCOPE='bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5'
COMMIT='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
META=['manifest.json','seal.json']
FORMAL='510548427d70b08ff90285e1ec90ba71cb29905a5ba674ce37902a6ff789cbef'
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(b):return hashlib.sha256(b).hexdigest()
def pairs(items):
    out={}
    for k,v in items:
        need(k not in out,'duplicate JSON key');out[k]=v
    return out
def parse(b):return json.loads(b,object_pairs_hook=pairs)
def safe_name(x,directory=False):
    need(isinstance(x,str) and x and '\\' not in x,'bad path')
    if directory and x=='.':return x
    p=PurePosixPath(x)
    need(not p.is_absolute() and p.as_posix()==x and all(v not in ('','..','.') for v in p.parts),'noncanonical path')
    need('__pycache__' not in p.parts and not x.endswith(('.pyc','.pyo')),'bytecode forbidden')
    return x
def no_symlink_ancestors(p):
    for q in [p,*p.parents]:need(not q.is_symlink(),'symlink ancestor')
def read(root,name):
    p=root/safe_name(name);no_symlink_ancestors(p)
    need(stat.S_ISREG(p.lstat().st_mode),'not a regular file')
    return p.read_bytes()
def inventory(root):
    no_symlink_ancestors(root);need(root.is_dir(),'missing root')
    files=set();dirs={'.'}
    for base,ds,fs in os.walk(root,followlinks=False):
        for name in ds:
            p=Path(base)/name;need(not p.is_symlink() and p.is_dir(),'unsafe directory')
            dirs.add(safe_name(p.relative_to(root).as_posix(),True))
        for name in fs:
            p=Path(base)/name;need(not p.is_symlink() and stat.S_ISREG(p.lstat().st_mode),'unsafe file')
            files.add(safe_name(p.relative_to(root).as_posix()))
    return files,dirs
def authenticate(root,anchor,counts=None):
    need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'bad external anchor')
    sb=read(root,'seal.json');need(digest(sb)==anchor,'external seal anchor mismatch')
    s=parse(sb);need(s['metadata']==META and s['scope_sha256']==SCOPE,'seal contract')
    mb=read(root,'manifest.json');need(len(mb)==s['manifest_size'] and digest(mb)==s['manifest_sha256'],'manifest identity')
    m=parse(mb);need(m['metadata']==META and m['upstream_commit']==COMMIT,'manifest contract')
    names=set()
    for e in m['files']:
        name=safe_name(e['path']);need(name not in names and name not in META,'duplicate/reserved member')
        names.add(name);b=read(root,name)
        need(len(b)==e['size'] and digest(b)==e['sha256'],'payload mismatch: '+name)
        need(bool(e['role']),'missing role')
    ds=[safe_name(x,True) for x in m['directories']]
    need(len(ds)==len(set(ds)) and '.' in ds,'duplicate/missing directory')
    actual_files,actual_dirs=inventory(root)
    need(actual_files==names|set(META) and actual_dirs==set(ds),'exact membership mismatch')
    need((len(actual_files),len(actual_dirs))==(s['owned_files'],s['owned_directories']),'count mismatch')
    if counts is not None:need(counts==(len(actual_files),len(actual_dirs)),'externally fixed count mismatch')
    return s,m

def audit(event,args):
    if event=='open':
        mode=args[1];flags=args[2]
        need(not isinstance(mode,str) or not any(c in mode for c in 'wax+'),'write forbidden')
        need(not isinstance(flags,int) or not flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND),'write flags forbidden')
    need(event not in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.symlink','os.link','os.truncate','subprocess.Popen','os.system'},'mutation/execution forbidden')
    need(not event.startswith('socket.'),'network forbidden')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);args=ap.parse_args()
 sys.addaudithook(audit)
 root=Path(__file__).absolute().parent;repo=root.parents[3]
 seal,manifest=authenticate(root,args.seal_sha256)
 need(seal['status']=='PASS_SCOPED_SUPPORT','verdict seal')
 status=parse(read(root,'status.json'));need(status['verdict']=='PASS_SCOPED_SUPPORT' and status['full_CDF098_formalized'] is False and status['count_change']==0 and status['published'] is False,'scope status')
 for e in parse(read(root,'external-inputs.json'))['files']:
  b=read(repo,e['path']);need(len(b)==e['bytes'] and digest(b)==e['sha256'],'external identity '+e['path'])
 p=root/'private/formal';raw=read(p,'output-manifest.json');need(digest(raw)==FORMAL,'formal anchor')
 fm=parse(raw);expected=set()
 for e in fm['files']:
  n=safe_name(e['path']);need(n not in expected and n!='output-manifest.json' and not n.startswith('.replays/'),'formal duplicate/reserved')
  expected.add(n);b=read(p,n);need(len(b)==e['bytes'] and digest(b)==e['sha256'],'copied formal payload')
 ff,dd=inventory(p)
 ff={x for x in ff if not x.startswith('.replays/')};dd={x for x in dd if x!='.replays' and not x.startswith('.replays/')}
 need(ff==expected|{'output-manifest.json'} and dd==set(fm['directories'])|{'.'},'copied baseline inventory')
 need(len(expected)==75,'formal payload count')
 source=read(p,'CDFLocal.lean');need(digest(source)=='1e4c558e4cd26e07094a06a40574a77b3453542c8b353311d211a81bdf578fdf','source hash')
 names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',source.decode(),re.M)
 thms=re.findall(r'^theorem (\w+)',source.decode(),re.M)
 cnames=re.findall(r'^theorem (\w+)',read(p,'Controls.lean').decode(),re.M)
 need((len(names),len(thms),len(cnames))==(39,30,11),'declaration counts')
 folder=p/'.replays/auditor-build';br=parse(read(folder,'receipt.json'))
 need(br['status'].startswith('PASS scoped source build') and br['previous_support_objects_used'] is False and br['full_CDF098_theorem_formalized'] is False,'build contract')
 need(br['support_declarations']==names and br['support_theorems']==thms and br['control_theorems']==cnames,'build declarations')
 for n,h in br['source_sha256'].items():need(digest(read(p,n))==h,'fresh build source')
 for key,ns,entries in [('axiom_reports','CDFLocal',names),('control_axiom_reports','CDFControls',cnames)]:
  report=br[key];need(set(report)=={ns+'.'+n for n in entries},'missing axiom report')
  need(all(set(a)<= {'propext','Classical.choice','Quot.sound'} for a in report.values()),'new axiom')
 for run in br['runs']:
  need(run['exit_code']==0,'failed fresh run')
  for suffix in ('stdout','stderr'):
   b=read(folder,run['name']+'.'+suffix);need(digest(b)==run[suffix+'_sha256'],'fresh output hash')
   need(not re.search(r'\b(?:SOME\s+FAIL|FAIL(?:ED)?|Traceback)\b|\berror:|warning:',b.decode(),re.I),'failure in success log')
 for name in ('types-axioms.stdout','example-types-axioms.stdout'):
  need(read(folder,name)==read(p/'logs/first-build',name),'type/axiom drift')
 mr=parse(read(p/'.replays/auditor-mutations','receipt.json'))
 need(mr['source_sha256']==digest(source) and len(mr['cases'])==6,'mutation source/count')
 for c in mr['cases']:
  b=read(p/'.replays/auditor-mutations',c['case']+'.stdout')
  need(c['exit_code']!=0 and c['result']=='EXPECTED_PROOF_REJECTION' and digest(b)==c['stdout_sha256'],'mutation rejection')
  t=b.decode();need(any(s in t for s in ('linarith failed','unsolved goals','omega could not prove')),'not proof rejection')
  need(not any(s in t for s in ('unknown module','unexpected token','Unknown identifier','Type mismatch','Application type mismatch')),'invalid mutant')
 cr=parse(read(root,'checks/independent-controls.json'));need(len(cr['cases'])==7,'independent controls')
 need(read(root,'checks/marker-child.stdout')==b'SOME FAIL\n' and b'exit=0' in read(root,'checks/wrapper.stderr'),'actual marker control')
 need([c['result'] for c in cr['cases']]==['REJECTED','ACCEPTED','REJECTED','REJECTED','REJECTED','REJECTED','ACCEPTED'],'negative control pattern')
 print(json.dumps({'result':'INTEGRITY_ONLY','recorded_verdict':'PASS_SCOPED_SUPPORT','own_files':seal['owned_files'],'own_directories':seal['owned_directories'],'formal_payloads':75,'fresh_support_theorems':30,'fresh_public_declarations':39,'fresh_controls':11,'mutants':6,'writes':0,'full_CDF098_formalized':False,'count_change':0},sort_keys=True))
if __name__=='__main__':
 try:main()
 except (ValueError,KeyError,OSError,TypeError) as exc:raise SystemExit('REJECT: '+str(exc))
