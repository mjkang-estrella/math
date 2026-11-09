import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent
pat=re.compile(r'Babai|distinguish|episturm|corolla|Chapoton|Shigechi|Temperley|Nilli|cubic|Panyushev|near.?factor|graphical|separat|Francisco|monochromatic|Norine|Gourmelon|Sklyar',re.I)
out={}
for p in (B/'expanded-corpus-r252/http').glob('*'):
 if p.name.endswith('.receipt.json'):continue
 if 'tree' in p.name:
  try:j=json.loads(p.read_text())
  except:continue
  hits=[x['path'] for x in j.get('tree',[]) if pat.search(x['path'])];out[p.name]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':j.get('truncated'),'hits':hits}
 elif 'pool-index' in p.name or 'projects.yml' in p.name:
  hits=[s for s in p.read_text().splitlines() if pat.search(s)];out[p.name]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':hits}
for p in L.glob('*head.html'):
 s=p.read_text();shas=re.findall(r'"oid":"([0-9a-f]{40})"',s);out[p.name]={'oids':list(dict.fromkeys(shas))[:4]}
(L/'registry-screen.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2)[:21000])
