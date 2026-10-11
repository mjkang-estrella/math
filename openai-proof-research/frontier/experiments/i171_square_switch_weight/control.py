"""Preparation and exactly-once seal controls. Never used by diagnostic replay."""
import sys,json,hashlib
from pathlib import Path
OWN=Path(__file__).resolve().parent;ROOT=OWN.parents[2]
SOURCES=ROOT/'frontier/sources/i171_square_switch_weight'
REPORT=ROOT/'frontier/iterations/i171-square-switch-weight.md'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def output(path,data):path.write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
def entry(path,role):return {'path':str(path.relative_to(ROOT)),'sha256':sha(path),'size':path.stat().st_size,'role':role}

def prepare():
    assert not (OWN/'seal.json').exists(),'Never prepare after sealing'
    initial=json.loads((SOURCES/'context-initial.json').read_bytes())
    drift=[{'path':x['path'],'expected':x['sha256'],'actual':sha(ROOT/x['path']),'drift':x['sha256']!=sha(ROOT/x['path']),'context_only':True} for x in initial]
    output(SOURCES/'context-preparation.json',drift)
    external={}
    old=ROOT/'frontier/experiments/i170_quadrilateral_coefficient'
    for x in json.loads((old/'inventory.json').read_bytes())['files']:
        p=ROOT/x['path'];assert sha(p)==x['sha256'];external[x['path']]=entry(p,'ancestor bytes/data only')
    for x in json.loads((ROOT/'frontier/sources/i170_quadrilateral_coefficient/external-bindings.json').read_bytes())['files']:
        if x['role']=='context-only':continue
        p=ROOT/x['path'];assert sha(p)==x['sha256'];external[x['path']]=entry(p,'ancestor bytes/data only')
    for p in [old/'inventory.json',old/'seal.json',old/'prevalidation.json',ROOT/'frontier/iterations/i166-affine-span-braces.md']:
        external[str(p.relative_to(ROOT))]=entry(p,'ancestor bytes/data only')
    for x in initial:
        e=entry(ROOT/x['path'],'context-only');e['sha256']=x['sha256'];external[x['path']]=e
    output(SOURCES/'replay-policy.json',{'context_only_exclusions':[x['path'] for x in initial],'all_other_inputs':'hash enforced','ancestor_python':'never executable; data bytes only','guard':'writes, filesystem mutation, socket/network, subprocess, unbound reads, all outside compilation/execution, forged owned source; eight explicit probes','controls_excluded_from_inventory':['inventory.json','prevalidation.json','seal.json'],'control_chain':'seal binds inventory and successful prevalidation; detached final response supplies seal digest','report_self_digest':'detached in seal.json; cannot insert a digest of full report into the same hashed report without circularity'})
    controls={'inventory.json','prevalidation.json','seal.json'}
    files=[p for folder in (OWN,SOURCES) for p in folder.rglob('*') if p.is_file() and not (p.parent==OWN and p.name in controls)]+[REPORT]
    replays=[]
    specifications=[
        ('research.py','run',['mandatory'],'mandatory-attempt-01.json'),
        ('research.py','run',['audit'],'audit-attempt-02.json'),
        ('research.py','run',['coefficient-audit'],'coefficient-audit-attempt-02.json'),
        ('research.py','run',['long-audit'],'long-audit-attempt-01.json'),
        ('attack.py','attack',['certificates'],'certificates-attempt-01.json'),
        ('guide.py','guide',[],'guide-attempt-01.json'),
        ('attack.py','attack',['weights'],'weights-attempt-01.json'),
        ('weight_obstruction.py','obstruction',[],'weight-obstruction-attempt-01.json'),
        ('brace_certificate.py','brace_certificate',[],'brace-certificate-attempt-01.json'),
        ('attack.py','attack',['octagons'],'octagons-attempt-01.json'),
        ('targeted.py','targeted',[],'targeted-attempt-01.json')]
    for mod,fn,args,payload in specifications:replays.append({'module':mod,'function':fn,'args':args,'payload':str((OWN/payload).relative_to(ROOT))})
    output(OWN/'inventory.json',{'iteration':171,'report':str(REPORT.relative_to(ROOT)),'files':[entry(p,'owned source' if p.suffix=='.py' else 'owned report or payload') for p in sorted(files)],'external':list(sorted(external.values(),key=lambda x:x['path'])),'replays':replays})
    print(json.dumps({'inventory_sha256':sha(OWN/'inventory.json'),'report_sha256':sha(REPORT),'verifier_sha256':sha(OWN/'verify.py'),'owned':len(files),'external':len(external)}))

def seal():
    assert not (OWN/'seal.json').exists(),'Never reseal'
    inv=json.loads((OWN/'inventory.json').read_bytes());pv=json.loads((OWN/'prevalidation.json').read_bytes());assert pv['status']=='PASS' and pv['mode']=='prevalidation'
    assert pv['inventory_sha256']==sha(OWN/'inventory.json') and pv['report_sha256']==sha(REPORT) and pv['verifier_sha256']==sha(OWN/'verify.py')
    for x in inv['files']+inv['external']:
        if x['role']!='context-only':assert sha(ROOT/x['path'])==x['sha256']
    data={'iteration':171,'creation':'exclusive-create once after successful --prevalidate; never reseal','report_sha256':sha(REPORT),'verifier_sha256':sha(OWN/'verify.py'),'inventory_sha256':sha(OWN/'inventory.json'),'prevalidation_sha256':sha(OWN/'prevalidation.json')}
    with (OWN/'seal.json').open('x') as f:f.write(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(data,seal_sha256=sha(OWN/'seal.json')),sort_keys=True))

if __name__=='__main__':
    {'--prepare':prepare,'--seal':seal}[sys.argv[1]]()
