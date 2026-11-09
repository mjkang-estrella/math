import pathlib,json,re,sys,hashlib
D=pathlib.Path(sys.argv[1]);o=json.loads((D/'outputs/registry-screen.json').read_text());ex=json.loads((D/'extracted.json').read_text());terms=[*ex]+[x['source_url'].rsplit('/',1)[1] for x in ex.values()]+['Bao','Kashima','Gheeraert','Romana','Stipulanti','Chen','Yuan','Zahar','friends-and-strangers','triangular lattice','dominated number']
o['screen_terms']=terms;o['hits']=[]
for p in (D/'sources').glob('pool-*/body'):
 s=p.read_text()
 for t in terms:
  for m in list(re.finditer(re.escape(t),s,re.I))[:5]:o['hits'].append({'file':str(p.relative_to(D)),'term':t,'context':s[max(0,m.start()-100):m.start()+250]})
o['github_searches']=[{'receipt':str(p.parent.relative_to(D)),'total_count':json.loads(p.read_text()).get('total_count')} for p in (D/'sources').glob('github-search-*/body')]
o['search_hit_disposition']='Triangular-Lattice-Coulomb-Lean README describes Coulomb lattice sums, not distance sets. Lean Pool broad-name matches are noisy and do not certify clearance.'
o['limitations']='OpenAI and Omega root recursive trees are truncated. Omega D5 subtree fetched separately; path screens are not proof-body audits. No global prior-art clearance.'
(D/'outputs/registry-screen.json').write_text(json.dumps(o,indent=2))
