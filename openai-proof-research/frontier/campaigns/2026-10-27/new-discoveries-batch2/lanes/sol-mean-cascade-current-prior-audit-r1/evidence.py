exec((__import__('pathlib').Path(__file__).parent/'audit.py').read_text().split("if sys.argv[1] in")[0])
inputs=['root-log-arctangent-candidate-r1/PROOF.md','root-cascade-rate-candidate-r1/PROOF.md','root-log-arctangent-candidate-r1/review-freeze.json','root-cascade-rate-candidate-r1/review-freeze.json','root-log-arctangent-source-r3/SOURCE-REVIEW.md','root-log-arctangent-source-r3/sources/publisher-canonical.txt','sol-log-arctangent-source-subsumption-r1/review.md','sol-log-arctangent-investment-review-r3/review.md','sol-log-arctangent-source-subsumption-r1/stolarsky-2011.txt','sol-log-arctangent-source-subsumption-r1/mean-convexity.txt','sol-log-arctangent-source-subsumption-r1/refinements-2012.txt','sol-log-arctangent-source-subsumption-r1/chen-ratio.txt','sol-cascade-rate-preliminary-review-r1/review.md','sol-cascade-source-prior-review-r2/review.md','sol-cascade-source-prior-review-r2/sources/supplement-2021.pdf','sol-cascade-source-prior-review-r2/sources/supplement-2021.txt','sol-cascade-source-prior-review-r2/sources/gallo2011.pdf','sol-cascade-source-prior-review-r2/sources/gallo2011.txt','sol-cascade-rate-preliminary-review-r1/sources/nonregular.txt','sol-cascade-rate-preliminary-review-r1/sources/vlmc2012.txt','sol-cascade-rate-preliminary-review-r1/sources/kraft.txt','root-cascade-rate-candidate-r1/sources/cascade-journal.pdf','root-cascade-rate-candidate-r1/sources/cascade-journal.txt','root-cascade-rate-candidate-r1/sources/companion-2019.txt']
r=[]
for s in inputs:
 p=lanes/s;r.append({'path':str(p),'sha256':D(p.read_bytes()),'bytes':p.stat().st_size})
(b/'cached-evidence-hashes.json').write_text(json.dumps(r,indent=2))
# Independently compare complete old and new trees; this is corroborative, not our completeness basis.
r={}
for part in ['D5','Problems']:
 old=json.loads((lanes/'sol-cascade-rate-preliminary-review-r1/sources'/('omega-'+part+'.json')).read_text());new=json.loads((b/'sources'/('omega-'+part+'-tree.json')).read_text());assert not old['truncated'] and not new['truncated']
 a={e['path']:e['sha'] for e in old['tree']};z={e['path']:e['sha'] for e in new['tree']}
 r[part]={'added':[p for p in z if p not in a],'deleted':[p for p in a if p not in z],'changed':[p for p in z if p in a and z[p]!=a[p]]}
(b/'complete-tree-delta.json').write_text(json.dumps(r,indent=2))
terms=json.loads((b/'path-screen.json').read_text())
import re
screens={}
for n in ['openai-CONTENTS.md','count-registry.json']:
 s=(b/'sources'/n).read_text();ts=['2405.13618','2004.07893','bej1299','mihok','raiss','raïss','cenac','cénac','pouyanne','arctan','stolarsky','cascade','context tree','variable length','stabilizab']
 screens[n]={t:[s[max(0,m.start()-100):m.start()+250] for m in re.finditer(re.escape(t),s,re.I)] for t in ts}
(b/'catalogue-screen.json').write_text(json.dumps(screens,indent=2));print('cached sources',len(inputs),'delta', {k:{t:len(v) for t,v in a.items()} for k,a in r.items()})
