#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Read-only identity and gate mutation controls; never modifies canonical inputs."""
import copy,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
from bundle_common import *
p=Path(__file__).resolve().parent
root=p if (p/'frontier').exists() else p.parents[3]
s=parse((p/'payload-selection.json').read_bytes());g=parse((p/'FINAL-GATE.json').read_bytes())
data={r['path']:read(root,r['path']) for r in s['files']+g['artifacts']}
results=[]
def test(label,fn,positive=False):
    try:fn();ok=positive
    except (ValueError,KeyError,StopIteration,OSError,TypeError):ok=not positive
    require(ok,'control failed: '+label);results.append(dict(name=label,pass_=ok))
test('positive',lambda:verify_inputs(data.__getitem__,s,g),True)
for key,value in [('status','PENDING'),('accepted',True),('published',True),('count_change',1),('full_T117Q_formalized',True),('full_claim_unchanged',False),('source_pin','0'*40),('scope_sha256','0'*64),('candidate_sha256','0'*64),('artifacts',[]),('parent_adoption',{})]:
    q=copy.deepcopy(g);q[key]=value;test(key,lambda:verify_inputs(data.__getitem__,s,q))
for name in g['anchors']:
    q=copy.deepcopy(g);q['anchors'][name]=None;test('missing gate anchor '+name,lambda:verify_inputs(data.__getitem__,s,q))
    path='frontier/campaigns/2026-10-14/'+name+'/'+g['anchors'][name]['file']
    d=dict(data);d[path]+=b' ';test('changed anchor bytes '+name,lambda:verify_inputs(d.__getitem__,s,g))
for verdict in g['verdicts']:
    q=copy.deepcopy(g);q['verdicts'][verdict]='FORGED';test('verdict '+verdict,lambda:verify_inputs(data.__getitem__,s,q))
for path in [s['files'][0]['path'],g['artifacts'][0]['path'],g['parent_adoption']['path']]:
    d=dict(data);del d[path];test('missing payload '+path,lambda:verify_inputs(d.__getitem__,s,g))
    d=dict(data);d[path]+=b'x';test('changed payload '+path,lambda:verify_inputs(d.__getitem__,s,g))
q=copy.deepcopy(s);q['files'].append(q['files'][0]);test('duplicate selection',lambda:verify_inputs(data.__getitem__,q,g))
for path in ['../escape','/absolute','private/body.txt','cache/file','x/__pycache__/x.pyc']:
    test('unsafe '+path,lambda:public_path(path))
print(json.dumps(dict(status='PASS',controls=len(results),results=results),indent=2))
