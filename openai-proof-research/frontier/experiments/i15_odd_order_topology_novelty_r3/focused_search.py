from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i15_odd_order_topology_novelty_r3';C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
m=json.loads((C.parent/'corpus-manifest.json').read_text())
patterns={
 'topology_realization':r'Nielsen|(?:outer.{0,20}automorphism|homotopy.{0,15}equivalence).{0,250}(?:reali[sz]|homeomorphism)|(?:unreali[sz]|nonreali[sz]).{0,100}(?:manifold|topolog)',
 'marked_arity':r'grope|marked.{0,10}bod|tip.{0,10}annul|(?:arbitrary|general|finite).{0,100}(?:law family|commutator tree|cap.selection)',
 'odd_topology':r'(?:odd.{0,8}(?:order|prime)|order.{0,8}(?:three|3)|cyclic.{0,8}cover).{0,300}(?:manifold|grope|homeomorphism|Nielsen)|(?:manifold|grope|homeomorphism|Nielsen).{0,300}(?:odd.{0,8}(?:order|prime)|order.{0,8}(?:three|3)|cyclic.{0,8}cover)',
}
hits=[]
for f in m['files']:
 t=re.sub(r'\s+',' ',(C/f['path']).read_text(errors='replace'))
 for k,pat in patterns.items():
  for z in re.finditer(pat,t,re.I):hits.append({'pattern':k,'path':f['path'],'normalized_offset':z.start(),'context':t[max(0,z.start()-150):z.end()+250]})
(S/'normalized-search.json').write_text(json.dumps({'patterns':patterns,'hits':hits,'limits':'Whitespace normalized text screen; not semantic exhaustion.'},indent=2)+'\n')
for k in patterns:print(k,sorted({x['path'].split('/')[1] for x in hits if x['pattern']==k}))
