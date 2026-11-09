exec(compile(open('investigate.py').read().split("mode=sys.argv[1]")[0],'caps','exec'))
terms=['permutation trinomial','quasi-dihedral','connectivity function','subtraction game','shifted Young','phase tropical','polynomial factor','cluster algebra','Carnevale','edge-isoperimetric','spectral partition','functional digraph','multiline queue','plane permutation','large spectrum']
files=[pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]
files += [L/'sources'/n for n in ['openai-current-CONTENTS.md','leanpool-projects.yml','leanpool-index.lean']]
rows=[]
for p in files:
 if not p.exists():continue
 s=p.read_text();hits=[]
 for t in terms:
  for m in re.finditer(re.escape(t),s,re.I):hits.append({'term':t,'offset':m.start(),'context':s[max(0,m.start()-250):m.end()+550]})
 rows.append({'path':str(p),'sha256':sha(s.encode()),'depth':'routing/title/abstract only; no theorem inferred','hits':hits});print(str(p),json.dumps(hits,ensure_ascii=False))
js('registry-routing-review.json',rows)
for n in ['openai-current.html','leanpool-current.html']:
 p=L/'sources'/n
 if p.exists():
  s=p.read_text();heads=re.findall(r'currentOid.{0,100}|committedDate.{0,100}',s);print(n,heads[:8]);js('registry-head-'+n+'.json',{'matches':heads[:8],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limitation':'HTML head only, no git API'})
receipt('inspect-indexes',{'true_exit':0})
