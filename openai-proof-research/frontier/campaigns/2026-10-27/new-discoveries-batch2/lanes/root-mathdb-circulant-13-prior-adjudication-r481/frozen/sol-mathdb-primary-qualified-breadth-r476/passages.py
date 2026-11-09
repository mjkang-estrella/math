import pathlib,re,json
D=pathlib.Path(__file__).resolve().parent;out=[]
for p in sorted((D/'sources').glob('*.txt')):
 lines=p.read_text().splitlines(); hits=[i for i,l in enumerate(lines) if re.match(r'^\s*(Conjecture|CONJECTURE|Question|Problem)\s+\d',l)]
 if not hits:hits=[i for i,l in enumerate(lines) if re.search('conjecture|question',l,re.I)][:2]
 spans=[]
 for i in hits[:5]:
  a=max(0,i-2);b=min(len(lines),i+16);spans.append({'start_line':a+1,'end_line':b,'text':'\n'.join(lines[a:b])})
 out.append({'file':str(p.relative_to(D)),'version':next((l.strip() for l in lines[:45] if 'arXiv:' in l),'not extracted'),'passages':spans,'scope':'selected question passages, not whole body or proof audit'})
(D/'passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for k in range(3):
 with (D/f'passages-{k+1}.txt').open('w') as f:
  for x in out[k*16:(k+1)*16]:
   f.write('\n'+x['file']+' '+x['version']+'\n')
   for s in x['passages']: f.write(f"L{s['start_line']}-{s['end_line']}\n"+s['text']+'\n')
print(len(out),'source texts; excerpts generated, not proof audits')
