import pathlib,json,hashlib,re
L=pathlib.Path(__file__).resolve().parent;h=lambda b:hashlib.sha256(b).hexdigest();log=[]
for p in sorted(L.glob('openai-finalbranch-*.body')):
 d=json.loads(p.read_text());log.append(p.name+' truncated='+str(d.get('truncated'))+' entries='+str(len(d['tree'])))
 for e in d['tree']:
  if re.search(r'semiacyclic|bordeaux|soliton|gilbreath|stirling|twostack|two.stack|wilf|zerodivisor|zero.divisor|treelike|tree.like|peakcount|peak.count|treeable|quasisymmetric',e['path'],re.I):log.append(e['path'])
(L/'final-branch-screen.txt').write_text('\n'.join(log)+'\n');print('\n'.join(log)[:8000])
r=json.loads((L/'results.json').read_text());assert len(r)==20
for i,v in r.items():
 raw=(L/(i+'.raw.jsonl')).read_bytes();d=json.loads(raw);assert h(raw)==v['provenance']['raw_sha256'];assert d['statement']==v['statement_literal'];assert h(d['statement'].encode())==v['provenance']['statement_sha256'];assert v['accepted_credit']==0
print('PASS: twenty exact literals, raw newline hashes, statement hashes and zero credits')
