from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[3];O=R/'frontier/sources/i07_structures';base=O/'upstream'
manifest=json.loads((O/'retrieval-manifest.json').read_text());records=[]
sel={
'A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026':{'prop:edge-potential','lem:edge-based-slice','thm:edge-algebraicity','prop:formal-trace-comparison','lem:tensor-nilpotent-correction','lem:vertex-adjoint-span'},
'Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026':{'thm:pair','thm:self-map','cyc:criterion','refl:input','refl:chamber-data','refl:cover-comparison','ch:four-tip-model','ch:laws','ch:exterior-model','ch:homotopy-type','ch:exterior-duals','ch:poincare-chamber','ch:boundary-surjectivity','ch:cover-data','ch:even-filling','for:cuts','for:linear','for:formal-data','for:edge-input','ten:assignment','ten:odd-cycle'},
'Exponential-PSD-rank-of-positively-shifted-matching-matrices-October-5-2026':{'thm:main','cor:exact-lift'},
'A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026':{'thm:main','prop:model'},
'Simple-F-infinity-overgroups-of-groups-with-decidable-word-problem-September-23-2026':{'thm:main'},
'An-infinite-finitely-presented-periodic-group-September-23-2026':{'thm:main','cor:kazhdan'},
'An-infinite-finitely-presented-residually-finite-2-group-October-5-2026':{'thm:main'},
'Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026':{'thm:main'},
'A-PD4-group-without-an-aspherical-manifold-model-September-24-2026':{'thm:main'}}
for m in manifest:
 name=m['path'].split('/')[1]
 if name not in sel:continue
 s=(base/m['path']).read_text()
 for label in sorted(sel[name]):
  needle=r'\label{'+label+'}';idx=s.find(needle)
  if idx<0:continue
  starts=list(re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}',s[:idx]))
  if not starts:continue
  st=starts[-1];end=s.find(r'\end{'+st[1]+'}',idx)+len(r'\end{'+st[1]+'}')
  text=s[st.start():end]
  records.append(dict(path=m['path'],url=m['url'],source_sha256=m['sha256'],label=label,start_line=s.count('\n',0,st.start())+1,end_line=s.count('\n',0,end)+1,statement=text,statement_sha256=hashlib.sha256(text.encode()).hexdigest()))
(O/'theorem-contracts.json').write_text(json.dumps(records,indent=2)+'\n')
s=(R/'sources/CONTENTS.md').read_text();ranges=[(32,69),(102,142),(155,210),(240,259),(285,320)]
heads=[(int(n),title) for n,title in re.findall(r'\*\*(\d+)\. (.*?)\*\*',s)]
(O/'broad-screen-headings.json').write_text(json.dumps([dict(family=n,title=t) for n,t in heads if any(a<=n<=b for a,b in ranges)],indent=2)+'\n')
print('Exact statement contracts:',len(records))
