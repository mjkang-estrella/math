import pathlib,json,re,sys,importlib.util,html
D=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('lanehttp',D/'scripts/http.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def clean(s):return html.unescape(re.sub('<[^>]+>',' ',s))
meta={}
for p in sorted((D/'sources').glob('abs-*')):
 a=p.name[4:];s=(p/'body').read_text();(p/'text.txt').write_text(clean(s))
 versions=sorted(set(re.findall(a+r'v(\d+)',s)),key=int)
 def field(c):
  z=re.search('<td class="tablecell '+c+'">(.*?)</td>',s,re.S);return clean(z[1]).strip() if z else None
 meta[a]={'versions':versions,'journal':field('jref'),'doi':field('doi'),'title':clean(re.search('<title>(.*?)</title>',s,re.S)[1])}
 print(a,meta[a],flush=True)
(D/'outputs/source-metadata.json').write_text(json.dumps(meta,indent=2))
if len(sys.argv)>1:
 for a,m in meta.items():
  for v in m['versions']:
   if not (D/'sources'/('pdf-'+a+'v'+v)).exists():h.get('pdf-'+a+'v'+v,'https://arxiv.org/pdf/'+a+'v'+v)
