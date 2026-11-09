import json,pathlib,re,html
D=pathlib.Path(__file__).resolve().parents[1];vs=json.loads((D/'outputs/version-inventory.json').read_text());out={}
for i,v in vs.items():
 excerpts={}
 for ver in v['versions']:
  s=(D/f'sources/{i}-v{ver}.txt').read_text()
  excerpts[ver]=[s[max(0,m.start()-80):m.start()+600] for m in re.finditer(r'Conjecture\s+[\dA-Z][\d.]*\.',s)]
 out[i]=excerpts
 s=(D/f'sources/{i}-abs.body').read_text()
 j=re.search(r'class="metatable">(.*?)</div>',s,re.S)
 print(i,'JOURNAL',html.unescape(re.sub('<[^>]+>',' ',j.group(1)))[:1000] if j else 'none')
 print('\n'.join(excerpts[v['versions'][-1]])[:2800])
(D/'outputs/all-version-excerpts.json').write_text(json.dumps(out,indent=2))
