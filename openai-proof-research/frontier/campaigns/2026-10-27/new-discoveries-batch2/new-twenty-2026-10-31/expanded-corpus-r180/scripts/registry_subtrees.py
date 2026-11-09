import pathlib,runpy,json,re
D=pathlib.Path(__file__).resolve().parents[1];m=runpy.run_path(str(D/'scripts/fetch.py'));fetch=m['fetch'];r=json.loads((D/'outputs/registry-screen.json').read_text())
for repo,names in [('openai/math',['preprints']),('the-omega-institute/trureturing',['D5','Problems'])]:
 sha=r[repo]['head'];tag=repo.split('/')[-1]
 b=fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}',D/'sources'/f'{tag}-root.json')
 if not b:continue
 tree=json.loads(b)['tree'];print(tag,[x['path'] for x in tree],flush=True)
 for name in names:
  x=next((x for x in tree if x['path']==name),None)
  if not x:continue
  b=fetch(f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1',D/'sources'/f'{tag}-{name}.json')
  if not b:continue
  t=json.loads(b);hits=[x['path'] for x in t['tree'] if re.search('golomb|lee.code|layered|quasi.kernel|saxton|supermagic|perfect.basis|zero.sum|cordial|gatex|inversion|Cichacz',x['path'],re.I)]
  r[repo][name]={'truncated':t.get('truncated'),'entries':len(t['tree']),'hits':hits};print(tag,name,'truncated',t.get('truncated'),'hits',hits[:35],flush=True)
r['subtree_receipts']=m['receipts'];(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2))
