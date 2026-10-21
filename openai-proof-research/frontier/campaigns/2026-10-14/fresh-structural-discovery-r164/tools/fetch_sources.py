from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r164')
J=json.loads((R/'private/source/selected-tree-entries.json').read_text())
chosen=[]
for e in J['entries']:
 p=e['path']
 if e['type']!='blob':continue
 islist='/A-linear-list-' in p
 if (islist and (p.endswith('.tex') or p.endswith('.bib')) and '/figures/' not in p and 'glyph-' not in p) or (not islist and (p.endswith('/main.tex') or p.endswith('/01-introduction.tex') or p.endswith('/references.bib') or p.endswith('/13-graph-transfer.tex') or p.endswith('/14-parameters.tex'))):chosen.append(e)
def run(e):
 p=e['path'];url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+p
 try:
  b=urllib.request.urlopen(url,timeout=35).read()
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==e['size'] and blob==e['sha'],(p,'identity mismatch')
  short='list' if '/A-linear-list-' in p else ('cdv' if '/A-counterexample-to-the-Colin-' in p else 'hadwiger')
  out=R/'private/source'/short/Path(p.split('/build/',1)[1]);out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b)
  return {'canonical_path':p,'url':url,'size':len(b),'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'copy':str(out.relative_to(R)),'status':'authenticated; semantic extent separately recorded'}
 except Exception as ex:return {'canonical_path':p,'url':url,'failure':str(ex)}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rows=list(ex.map(run,chosen))
(R/'private/source/authentication.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{'copy':x.get('copy'),'bytes':x.get('size'),'failure':x.get('failure')} for x in rows],indent=2))
