from pathlib import Path
import hashlib,json
base=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14'); dest=base/'t298p-release-development'
anchors={
'fresh-structural-discovery-r104':'b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3',
't298p-proof-r2':'eb7f9e3cb4c14ad5793906ff0f3f5b7288e8bfebc5cc72a0e160fcd6c7fdf87c',
't298p-contribution-r2':'31e84ba9937ddd232381af31d869f471b911e124cf786b43179c693e81576566',
't298p-attribution-r1':'27a968a7dcb796907e97e4d4c39a2bd0e978a0118fb3d05d2f51eb1671a5d6e3',
't298p-attribution-r2':'6c77938d8f46ef62dd2523dc4df749539ec22e45b4fa184e2a41516ba1a102a8',
't298p-formal-r1':'e8d1d16e4d90b53b9fbb2b469a40e63c1d8b1e67b3647448f37f33b0b1857400',
't298p-formal-review-r2':'e7deca3d35fd481ba7fa45242af7437c410e08c05cb7a118fc69292c7f142628',
't298p-manuscript-r1':'24a3e405e1bceda384a8b6a4e28f610809a4c9ec5b32b0a66e0277b24b2124fe'}
rows=[]
def add(pkg,name,out,role):
 raw=(base/pkg/name).read_bytes(); rec={'packet':pkg,'source':name,'destination':out,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'role':role};rows.append(rec)
for pkg,anchor in anchors.items():
 raw=(base/pkg/'MANIFEST.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==anchor
 add(pkg,'MANIFEST.json','attestations/'+pkg+'-MANIFEST.json','external original manifest; selected subset only')
pkg='t298p-manuscript-r1'
for name in ['main.tex','output/pdf/main.pdf','build.py','LICENSE-PAPER.txt','LICENSE-CODE.txt','THIRD-PARTY.md','provenance.md','reading-limits.md','required-item-map.md','validation/build-receipt.json','validation/build-console.log','validation/pdfinfo.txt','validation/visual-review.json','validation/reproduction.json','check_arithmetic.py','validation/arithmetic.json']:
 add(pkg,name,'paper/'+name,'complete manuscript or manuscript validation/rights')
for name in ['candidate.md','scope-freeze.md','matched-volume-attempt.md','unconditional-score-construction.md','normal-slice-construction.md','finite-entropy-chart.md','stress-checks.md','source-receipts.json','primary-receipts.json']:
 add('fresh-structural-discovery-r104',name,'proof/original/'+name,'historical frozen author argument; manuscript supersedes pending prose')
for pkg in ['t298p-proof-r2','t298p-contribution-r2']:
 add(pkg,'review.md','reviews/'+pkg+'/review.md','completed independent review of original candidate')
for pkg,name in [('t298p-attribution-r1','addendum.md'),('t298p-attribution-r2','response.md')]:
 add(pkg,name,'reviews/'+pkg+'/'+name,'author attribution response; not an independent review')
for name in ['T298P.lean','Controls.lean','rebuild.py','lake-manifest.json','lakefile.toml','lean-toolchain','coverage.md','LICENSE-CODE.txt']:
 add('t298p-formal-r1',name,'formal/author/'+name,'scoped author support, controls, runner and dependency locks')
for name in ['Checks.lean','support.log','controls.log','types-axioms.log','receipt.json']:
 add('t298p-formal-r1','validation/'+name,'formal/author/reference/'+name,'recorded author compilation reference')
for name in ['Independent.lean','audit.py','review.md','verdict.json','LICENSE-CODE.txt']:
 add('t298p-formal-review-r2',name,'formal/reviewer/'+name,'independent scoped audit source or completed review')
for name in ['Checks.lean','T298P.log','Controls.log','Independent.log','types-axioms.log','receipt.json']:
 add('t298p-formal-review-r2','independent-build/'+name,'formal/reviewer/reference/'+name,'independent replay reference')
for label in ['denominator-k2','no-column-gram','no-endpoint','reversed-gap','weak-error']:
 for ext in ['lean','log']:
  add('t298p-formal-review-r2','independent-build/'+label+'.'+ext,'formal/reviewer/negative-fixtures/'+label+'.'+ext,'intentional failing source fixture or expected rejection log; NOT a proved theorem')
for row in rows:
 if row['source']=='MANIFEST.json':continue
 mf=json.loads((base/row['packet']/'MANIFEST.json').read_text());fs=mf['files'];fs={r['path']:r for r in fs} if isinstance(fs,list) else fs;ref=fs[row['source']];assert row['sha256']==(ref if isinstance(ref,str) else ref['sha256'])
(dest/'selection.json').write_text(json.dumps({'schema':'t298p-selection-v1','source_pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','anchors':anchors,'files':rows},indent=2)+'\n')
print(len(rows),'selected files',sum(x['bytes'] for x in rows),'bytes')
