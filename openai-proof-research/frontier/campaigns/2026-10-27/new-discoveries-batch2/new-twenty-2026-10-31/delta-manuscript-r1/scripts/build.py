from pathlib import Path
import json,hashlib,shutil,textwrap,re
O=Path(__file__).resolve().parents[1];B=O.parent
r=json.loads((O/'recomputation.json').read_text())
repl={'input_order':len(r['pure_matrices'][0]),'states':r['states'],'arcs':r['legal_move_arcs'],'min':r['minimum_order'],'minima':r['labelled_minima'],'moves':len(r['witness_operations']),'last':r['witness_orders'][-1],'ends':', '.join(map(str,r['end_bases'])),'modules':r['packet_modules'],'chunks':r['closure_chunks']}
repl['edges']='\n'.join('  '.join(f'({a},{b})' for a,b in r['base_edges'][i:i+6]) for i in range(0,len(r['base_edges']),6))
repl['pure']='reduce at '+', '.join(map(str,r['pure_centres']))+'\norders '+ ' -> '.join(map(str,r['pure_orders']))
repl['matrix']='\n'.join(' '.join(map(str,row)) for row in r['pure_matrices'][-1])
repl['counts']='Order:  '+' '.join(f'{n:>5}' for n in r['states_by_order'])+'\nStates: '+' '.join(f'{n:>5}' for n in r['states_by_order'].values())
repl['witness']='\n'.join(f'{i+1}. {op} {arg}; order {r["witness_orders"][i]} -> {r["witness_orders"][i+1]}' for i,(op,arg) in enumerate(r['witness_operations']))
s=(O/'paper.template.md').read_text()
for k,v in repl.items():s=s.replace('@'+k+'@',str(v))
assert not re.search('@[a-z]+@',s);assert s.isascii()
(O/'paper.md').write_text(s)
# Portable, editable PostScript source with standard PDF core fonts.
ps=['%!PS-Adobe-3.0','%%Pages: 7','/S {moveto show} bind def']
qa=[]
def esc(s):return s.replace('\\','\\\\').replace('(','\\(').replace(')','\\)')
for num,page in enumerate(s.split('===PAGE==='),1):
 ps+=['%%Page: %d %d'%(num,num),'0.15 0.20 0.26 setrgbcolor','/Helvetica findfont 8 scalefont setfont',f'56 760 moveto (DRAFT  |  MathDB 352253  |  AI-assisted) show','0 setgray']
 y=731;code=False;linecount=0
 for line in page.strip().splitlines():
  if line=='```':code=not code;y-=3;continue
  heading=line.startswith('# ');quote=line.startswith('> ')
  if heading:line=line[2:]
  if quote:line=line[2:]
  font,size,leading=('Courier',9.3,12) if code else ('Helvetica-Bold',14,19) if heading else ('Times-Italic',10.7,13.3) if quote else ('Times-Roman',10.7,13.3)
  if not line:y-=6.5;continue
  lines=[line] if code else textwrap.wrap(line,76 if heading else 98,break_long_words=False,break_on_hyphens=False)
  ps.append(f'/{font} findfont {size} scalefont setfont')
  for ln in lines:
   assert y>48,(num,y,ln)
   ps.append(f'56 {y:.2f} moveto ({esc(ln)}) show');y-=leading;linecount+=1
 ps+=['/Helvetica findfont 8 scalefont setfont',f'56 30 moveto (Unaccepted draft - root review required) show',f'543 30 moveto ({num}) show','showpage']
 qa.append({'page':num,'body_lines':linecount,'lowest_next_baseline':y})
ps.append('%%EOF');(O/'paper.ps').write_text('\n'.join(ps)+'\n');(O/'receipts/layout.json').write_text(json.dumps(qa,indent=2)+'\n')
# Preserve selected sources plus all available retrieval receipts / primary context from independent review.
paths=[B/'delta-root-ruling-r1.json']
for name in ['delta-formal-r1','delta-formal-r2','delta-formal-r3']:
 for f in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','CHANGE-REPORT.md','REPRODUCE.md','results.json','changes.json','replay-table.csv','logs/development-incidents.txt','logs/change-verification.log']:
  p=B/name/f
  if p.is_file():paths.append(p)
for name in ['delta-review-r1','delta-fidelity-review-r1']:
 for f in ['REVIEW.md','review.json','recomputation.json','numerical.json','scripts/recompute.py','logs/recompute.log','logs/numerical.log','logs/web-search.json']:
  p=B/name/f
  if p.is_file():paths.append(p)
 if (B/name/'downloads').exists():
  paths.extend(p for p in (B/name/'downloads').rglob('*') if p.is_file())
for f in ['replay-result.json','registry-refresh.json','root-replay.out']:
 paths.append(B/'delta-parent-final-r2'/f)
paths.extend(p for p in (B/'delta-parent-final-r2/registries').iterdir() if p.is_file())
for f in ['sources/352253.raw.jsonl','sources/352253.pdf','sources/352253.txt','sources/352253.abs','sources/delta-journal.pdf','sources/delta-journal.txt','outputs/pure-dag.json','outputs/http.jsonl','results.json','CANDIDATE-352253.md']:
 paths.append(B/'expanded-corpus-r153'/f)
paths.extend((B/'expanded-corpus-r153/outputs').glob('delta*.json'))
receipt=[]
for p in sorted(set(paths)):
 rel=p.relative_to(B);dest=O/'sources'/rel;dest.parent.mkdir(parents=True,exist_ok=True);data=p.read_bytes();shutil.copyfile(p,dest)
 receipt.append({'original':str(rel),'copy':str(dest.relative_to(O)),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
raw=O/'sources/expanded-corpus-r153/sources/352253.raw.jsonl';shutil.copyfile(raw,O/'sources/352253.raw.jsonl')
(O/'receipts/source-copies.json').write_text(json.dumps(receipt,indent=2)+'\n')
# Bind additional selected provenance before any further use; all copying is read-only.
initial=json.loads((O/'inputs-before.json').read_text());extra={a['original']:a['sha256'] for a in receipt if a['original'] not in initial}
(O/'inputs-supplemental-before.json').write_text(json.dumps(extra,indent=2)+'\n')
print('Built source, pages',len(qa),'copies',len(receipt));print(qa)
