import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for x in json.loads((L/'statements.json').read_text()):
 d=x['record'];ident=d['source_url'].rsplit('/',1)[1];p=L/'sources'/f'{ident}.txt'
 if not p.exists():continue
 lines=p.read_text().splitlines();hits=[i for i,s in enumerate(lines) if re.search(r'conjectur|open problem|question|disprov',s,re.I)];ranges=[]
 for i in hits:
  a=max(0,i-2);b=min(len(lines),i+9)
  if ranges and a<=ranges[-1][1]:ranges[-1][1]=max(b,ranges[-1][1])
  else:ranges.append([a,b])
 text='\n'.join(f'LINES {a+1}-{b}\n'+'\n'.join(lines[a:b]) for a,b in ranges)
 q=L/'sources'/f'passages-{d["mathdb_id"]}.txt';q.write_text(text+'\n');out.append(dict(mathdb_id=d['mathdb_id'],path=str(q.relative_to(L)),selection='all conjecture/question/disproof keyword windows, 2 lines before/8 after; selection is not read coverage',ranges_1based=[[a+1,b] for a,b in ranges],sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
(L/'passage-index.json').write_text(json.dumps(out,indent=2)+'\n')
