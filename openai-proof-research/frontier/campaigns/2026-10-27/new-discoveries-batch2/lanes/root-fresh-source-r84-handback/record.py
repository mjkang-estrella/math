import datetime,hashlib,json
from fractions import Fraction as F
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;S=P.parent/'sol-fresh-source-discovery-r84'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
pr=json.loads((S/'provenance.json').read_text())
diff={d['path']:{'recorded':d['sha256'],'actual':sha(S/d['path'])} for d in pr['files'] if sha(S/d['path'])!=d['sha256']}
assert set(diff)<= {'finalize.log','finalize-guard.json'},diff
def distribution(ts):
 a=[F(1)]
 for t in ts:
  b=[F(0)]*(len(a)+1)
  for i,v in enumerate(a):b[i]+=v*(1-t);b[i+1]+=v*t
  a=b
 return a
left=distribution([F(1,4),F(3,4)])
right=distribution([F(3,4),F(1,4)])
mid=distribution([F(1,2),F(1,2)])
assert left==right==[F(3,16),F(5,8),F(3,16)]
assert mid==[F(1,4),F(1,2),F(1,4)]
# d=2 source volume has only middle exponent1, so constant cancels.
assert mid[1]<(left[1]+right[1])/2
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'decision':'EXCLUDE_ROUTINE_INTERPRETATION; source attribution HOLD','credit':0,'counts':[8,38],
 'root_read':'Full summary/discovery and actual cached Corollary3.1 product-volume display. Root independently convolved Bernoulli pmfs for interior d2 midpoint witness.',
 'routine_bridge':'At d2, the published product formula has exponents0,1,0. Natural independent-Bernoulli pullback is therefore a positive constant times theta1+theta2-2theta1theta2. Endpoints(1/4,3/4),(3/4,1/4) have factor5/8 versus midpoint1/2. No substantive theorem beyond formula specialization is needed.',
 'scope_hold':'Actual journal-only future-work theta-family and quantifiers remain unread; do not claim the journal source question refuted. No extension to a volume root or other family is assumed.',
 'all_dimension_result':'All-d Hessian derivation preserved as uncredited helper, not separately nominated or independently formally verified by root.',
 'other_screens':'Varentropy/Tsallis public resolutions are worker-reported prior exclusions; no new credit or fresh independent proof audit.',
 'matching_manifest_files':len(pr['files'])-len(diff),'manifest_mismatches':diff,
 'hash_qualification':'Any finalizer output mismatch is retained explicitly; source content remains as delivered. No all-hashes-match claim when mismatch list nonempty.',
 'source_sha256':sha(S/'sources/bernoulli-v1.pdf'),'discovery_sha256':sha(S/'discovery.md'),
 'resource_qualification':'Worker brief outside-lane temporary filename-list write disclosed and preserved. No shared research edit; heavy checks capped. Root runs under improved helper guard.',
 'external_actions_performed':False}
(P/'EXCLUSION.json').write_text(json.dumps(out,indent=2)+'\n')
ledger=json.loads((B/'ledger.json').read_text());assert ledger['accepted_count']==8 and ledger['total_accepted_count']==38
key='bernoulli-fiber-volume-independent-pullback'
assert not any(e.get('id')==key for e in ledger['excluded'])
ledger['excluded'].append({'id':key,'status':'EXCLUDED_ROUTINE_INTERPRETATION_SOURCE_HOLD','credit':0,'reason':out['routine_bridge'],'scope_note':out['scope_hold'],'decision':'lanes/root-fresh-source-r84-handback/EXCLUSION.json'})
(B/'ledger.json').write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
n=(B/'NEXT.md').read_text().replace('fresh analysis/probability r84,','fresh analysis/probability r86,')
marker='r79 lasso separation';assert marker in n
n=n.replace(marker,'r84 Bernoulli fiber-volume independent-parameter interpretation is EXCLUDED as a routine d2 specialization of source Corollary3.1. Actual journal-question attribution remains HOLD; no claim of that question resolved. See root-fresh-source-r84-handback/EXCLUSION.json.\n'+marker,1)
(B/'NEXT.md').write_text(n)
paths=[p for p in S.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths.extend([P/'record.py',P/'EXCLUSION.json',P/'pathspec.txt',B/'NEXT.md',B/'ledger.json'])
(P/'pathspec.txt').write_text(''.join(str(p.relative_to(B.parents[4]))+'\n' for p in sorted(paths)))
print(json.dumps({'decision':out['decision'],'matching':out['matching_manifest_files'],'mismatches':diff,'counts':[8,38]}))
