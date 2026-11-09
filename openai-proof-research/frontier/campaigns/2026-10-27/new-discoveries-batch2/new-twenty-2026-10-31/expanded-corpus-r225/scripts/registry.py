import pathlib,json,importlib.util,re
D=pathlib.Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('fetch',D/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
for key,repo in [('leanpool','Vilin97/lean-pool'),('openai','openai/math'),('omega','the-omega-institute/trureturing')]:
 p=D/f'sources/{key}-head.json'
 if not p.exists():continue
 o=json.loads(p.read_text());sha=o['sha'];print(key,sha,flush=True)
 print(f.get(key+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1'),flush=True)
 p=D/f'sources/{key}-tree.json'
 if not p.exists():continue
 t=json.loads(p.read_text());pat=re.compile('onan|unital|dragon|graft|angle|cordial|kerdock|excedan|immersion|quasikernel|norton|kite|okrasa|hamilton|redundan',re.I)
 hits=[z for z in t.get('tree',[]) if pat.search(z['path'])]
 (D/f'sources/{key}-hits.json').write_text(json.dumps({'head':sha,'truncated':t.get('truncated'),'hits':hits},indent=2)+'\n')
 print('hits',len(hits),[z['path'] for z in hits][:50],flush=True)
