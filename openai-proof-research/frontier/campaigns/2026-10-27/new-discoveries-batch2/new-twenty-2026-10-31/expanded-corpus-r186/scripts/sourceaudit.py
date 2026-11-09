import pathlib,json,re,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186');out={}
for i,r in json.loads((L/'outputs/versions.json').read_text()).items():
 out[i]={}
 for v in r['versions']:
  p=next((L/'sources').glob('*-'+i+'-v'+v+'-pdf.txt'));s=p.read_text();lines=s.splitlines();hits=[]
  for n,line in enumerate(lines):
   if re.search(r'(Conjecture [0-9]|conjecture.*depend|conjecture.*regular)',line,re.I):hits.append({'line':n+1,'text':'\n'.join(lines[max(0,n-1):n+9])})
  out[i][v]={'pdf':str(p.with_suffix('.body')),'pdf_sha256':hashlib.sha256(p.with_suffix('.body').read_bytes()).hexdigest(),'text':str(p),'text_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'conjecture_excerpts':hits}
(L/'outputs/source-version-audit.json').write_text(json.dumps(out,indent=2))
print('audit',len(out),'sources',sum(len(v) for v in out.values()))
