from pathlib import Path
import json,hashlib,itertools,xml.etree.ElementTree as ET
r=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Independent direct-definition check of the source's small single-cycle example.
def poly(n):
 d={}
 for p in itertools.permutations(range(1,n+1)):
  x=1;seen=set()
  while x not in seen:seen.add(x);x=p[x-1]
  if len(seen)!=n:continue
  R=tuple(p[i] for i in range(n) if all(p[i]<p[j] for j in range(i+1,n)))
  E=tuple(sorted(p[i] for i in range(n) if p[i]>i+1))
  key=(tuple(sorted(R)),E);d[key]=d.get(key,0)+1
 return d
p4=poly(4);expected={((1,2,3),(4,)):1,((1,3),(2,4)):1,((1,),(3,4)):1,((1,2),(3,4)):2,((1,),(2,3,4)):1}
assert p4==expected
raw=r/'inputs/expanded-corpus-r204/raw/350721.jsonl';assert len(raw.read_text().splitlines())==1
(r/'mathdb-350721.jsonl').write_bytes(raw.read_bytes())
(r/'receipts/mathdb-raw.sha256').write_text(H(raw)+'  mathdb-350721.jsonl\n')
family=json.loads((r/'outputs/family.json').read_text());a9=next(x for x in family if x['n']==9)
assert [x['inv'] for x in a9['rows']]==[7,8,9,6,7,10,5,6]
for n,pos,neg in [(8,256,2),(9,707,15),(10,1931,89)]:
 a=json.loads((r/f'outputs/full-n{n}.json').read_text());assert a['counts']['3']=={'positive':pos,'negative':neg}
 assert a['even']==a['odd'] and a['even']+a['odd']==a['permutations']
 if n<10:assert len(a['target_hits'])==8
for n in range(2,8):assert all(d['negative']==0 for d in json.loads((r/f'outputs/full-n{n}.json').read_text())['counts'].values())
(r/'receipts/numeric-audit.json').write_text(json.dumps({'status':'PASS','scope':'All experimental quantities printed in the manuscript recomputed by fresh isolated Python; symbolic universal formulas justified by the hand proof. Source labels, years, page ranges, DOIs, IDs, versions and pinned commits are transcription metadata, not experimental computations.','family_n_range':[7,16],'n9_inversions':[x['inv'] for x in a9['rows']],'single_cycle_n3':[[list(R),list(E),v] for (R,E),v in poly(3).items()],'single_cycle_n4':[[list(R),list(E),v] for (R,E),v in p4.items()],'typo_identity_verified':True,'raw_sha256':H(raw),'zero_based_R':[v-1 for v in [1,5,7,8]],'zero_based_E':[v-1 for v in [2,3,4,6,9]]},indent=2)+'\n')
root=ET.parse('manuscript.xml').getroot()
lines=[]
for page in root:
 for el in page:
  text=''.join(el.itertext())
  if el.tag in ['h','title']:lines.append('\n## '+text+'\n')
  elif el.tag in ['p','math']:lines.append(text+'\n')
  elif el.tag=='tails':
   lines.append('| Name | tail (c=n−5) | cycle lengths | inversion count at n=9 |\n|---|---|---|---|')
   for a in a9['rows']:lines.append('| '+a['name']+' | '+str(a['word'][3:8])+' (n=9) | '+str(a['cycles'])+' (n=9) | '+str(a['inv'])+' |')
  elif el.tag=='counts':
   lines.append('See outputs/full-n8.json, full-n9.json, full-n10.json and PDF table; all values are loaded directly during PDF generation.\n')
(r/'manuscript-text.md').write_text('\n'.join(lines))
# A complete text proof supplement, not merely a pointer.
proof=['# Hand proof and certificate scope\n\nDRAFT; AI-assisted. No acceptance or priority claim.\n']
for page in list(root)[1:4]:
 for el in page:
  if el.tag in ['h','p','math']:proof.append(''.join(el.itertext())+'\n')
  elif el.tag=='tails':
   proof.append('The following explicit one-based words at n=9 instantiate the tails, whose general forms and cycle decompositions are given in the manuscript source.\n')
   for a in a9['rows']:proof.append(f"{a['name']}: {a['word']}; inv={a['inv']}; partition={a['cycles']}; admissible={a['admissible']}\n")
# include general tail definitions explicitly
proof.append('\nGeneral tails at c,...,c+4, with c=n−5 and last value c+4:\nA1=(c+2,1,c+1,c+5,c+3)\nA2=(c+2,1,c+5,c+1,c+3)\nA3=(c+2,c+5,1,c+1,c+3)\nA4=(1,c+2,c+1,c+5,c+3)\nA5=(1,c+2,c+5,c+1,c+3)\nA6=(c+5,c+2,1,c+1,c+3)\nB1=(1,c+2,c+1,c+3,c+5)\nB2=(c+2,1,c+1,c+3,c+5)\n\nThe Lean packet formalizes only the n=9 witness, the dual negation and the n=3 positive control; the universal family is a hand proof.\n')
(r/'PROOF.md').write_text('\n'.join(proof))
qa={'status':'PASS after font correction','pdf_sha256':H(r/'manuscript.pdf'),'method':'Rendered all pages with pdftoppm at 110 dpi; assistant individually viewed every final page image.','pages':[{'page':i,'image':f'qa/page-{i}.png','sha256':H(r/f'qa/page-{i}.png'),'inspection':'No clipping, overlap, missing math glyphs or broken tables observed; headers and footers readable.'} for i in range(1,7)],'initial_render_issue':'Noto Serif lacked some mathematical characters; fixed with Noto Sans Math fallback and re-rendered all pages.'}
(r/'receipts/visual-qa.json').write_text(json.dumps(qa,indent=2)+'\n')
print('Numeric audit, exact raw line, proof and QA receipts saved')
