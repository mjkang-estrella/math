from fetch import get
import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];out={}
for name,repo,scope in [('openai','openai/math','preprints'),('omega','the-omega-institute/trureturing','Problems')]:
 root=json.loads((D/f'sources/{name}-root.json').read_text());row=next(x for x in root['tree'] if x['path']==scope);key=f'{name}-{scope}-complete.json';print(get((key,f"https://api.github.com/repos/{repo}/git/trees/{row['sha']}?recursive=1")),flush=True)
 t=json.loads((D/'sources'/key).read_text());pat=re.compile(r'375523|375601|375764|375860|375861|376198|382474|382484|366544|366685|366709|366891|367011|367110|367279|367560|367758|367836|367848|368077|pinwheel|folding|wreath|cylindric|Schubert|Duval|rational.base|formality|Johnson',re.I)
 hits=[x['path'] for x in t['tree'] if pat.search(x['path'])];out[name]={'truncated':t.get('truncated'),'paths':len(t['tree']),'path_hits':hits}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print(out)
