import pathlib,re,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());out={}
for i,o in x.items():
 s=o['source_url'].rsplit('/',1)[-1];p=D/f'sources/{s}.txt';lines=p.read_text().splitlines();matches=[j for j,l in enumerate(lines) if re.search(r'Conjecture|conjecture|verified|computational|confirmed',l)];seen=set();ss=[]
 for j in matches:
  for k in range(max(0,j-3),min(len(lines),j+20)):
   if k not in seen:ss.append(f'{k+1}: {lines[k]}');seen.add(k)
 (D/f'outputs/{i}-source-excerpts.txt').write_text('\n'.join(ss))
 out[i]={'source_text_lines':len(lines),'excerpts_lines':len(ss),'html_sha256':hashlib.sha256((D/f'sources/{s}.html').read_bytes()).hexdigest()}
(D/'outputs/excerpts-index.json').write_text(json.dumps(out,indent=2))
