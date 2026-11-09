import pathlib,json,re,html,hashlib
D=pathlib.Path(__file__).resolve().parents[1];out={}
for row in json.loads((D/'reservation.json').read_text())['rows']:
 i=str(row['mathdb_id']);s=(D/f'sources/{i}-abs.body').read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int);out[i]={'arxiv':row['source_url'].split('/')[-1],'versions':vs,'doi':re.findall(r'<meta name="citation_doi" content="(.*?)"',s),'files':[]}
 for v in vs:
  p=D/f'sources/{i}-v{v}.txt';rec=D/f'sources/{i}-v{v}.receipt.json';out[i]['files'].append({'version':v,'receipt':str(rec.relative_to(D)),'text':str(p.relative_to(D)) if p.exists() else None,'pdf_sha256':json.loads(rec.read_text()).get('sha256')})
(D/'outputs/versions.json').write_text(json.dumps(out,indent=2))
# Preserve pertinent sections of every version, rather than falsely calling entire papers read.
chunks=[]
for p in sorted((D/'sources').glob('*.txt')):
 lines=p.read_text().splitlines();ranges=[]
 for k,l in enumerate(lines):
  if re.search(r'Conjecture|conjecture|counterexample|first column|Bruhat|Theorem 1\.',l):ranges.append((max(0,k-3),min(len(lines),k+12)))
 used=set();chunks.append('\nFILE '+p.name+'\n')
 for lo,hi in ranges:
  for k in range(lo,hi):
   if k not in used:chunks.append(str(k+1)+': '+lines[k]+'\n');used.add(k)
(D/'outputs/primary-excerpts.txt').write_text(''.join(chunks))
print(json.dumps({i:{'versions':x['versions'],'doi':x['doi']} for i,x in out.items()},indent=2))
