from pathlib import Path
import cairo,json
D=Path(__file__).resolve().parents[1]; data=json.loads((D/'verification.json').read_text())
W,H=595.28,841.89; left=48; width=W-96
surface=cairo.PDFSurface(str(D/'paper.pdf'),W,H); ctx=cairo.Context(surface)
surface.set_metadata(cairo.PDF_METADATA_TITLE,'Three induced colours on the Möbius ladder M_12 — DRAFT')
def font(size=10.5,bold=False):
 ctx.select_font_face('Liberation Serif',cairo.FONT_SLANT_NORMAL,cairo.FONT_WEIGHT_BOLD if bold else cairo.FONT_WEIGHT_NORMAL);ctx.set_font_size(size)
def line(s,x,y):
 for ch in s:
  original=ctx.get_font_face(); glyph=ctx.get_scaled_font().text_to_glyphs(0,0,ch)[0][0][0]
  if glyph==0: ctx.select_font_face("STIX Two Math"); assert ctx.get_scaled_font().text_to_glyphs(0,0,ch)[0][0][0]!=0,ch
  advance=ctx.text_extents(ch).x_advance; ctx.move_to(x,y); ctx.show_text(ch); x+=advance;ctx.set_font_face(original)
def wrap(s,size,bold=False):
 font(size,bold); lines=[];cur=''
 for word in s.split():
  nxt=(cur+' '+word).strip()
  if ctx.text_extents(nxt).x_advance>width and cur:lines.append(cur);cur=word
  else:cur=nxt
 if cur:lines.append(cur)
 return lines
def table(n,edge=False):
 global y
 d=data[str(n)];font(9.7)
 if edge:
  rows=[['Cycle i']+[str(i) for i in range(2*n)],['Label']+list(map(str,d['labels'][:2*n])),['Chord i']+[str(i) for i in range(n)],['Label']+list(map(str,d['labels'][2*n:]))]
  cols=2*n+1; cw=width/cols
  for row in rows:
   for j,t in enumerate(row):line(t,left+j*cw+3,y)
   y+=18
 else:
  rows=[['Vertex','Incident labels','Sum']]+[[str(i),' + '.join(map(str,a)),str(s)] for i,(a,s) in enumerate(zip(d['incident_labels'],d['sums']))]
  for i,row in enumerate(rows):
   if i==0:font(10,True)
   else:font(10)
   for j,t in enumerate(row):line(t,left+[14,115,300][j],y)
   y+=15
 y+=4
pages=(D/'paper.md').read_text().split('---PAGE---');receipt=[]
for pn,page in enumerate(pages,1):
 y=48;ctx.set_source_rgb(.1,.1,.12)
 font(8.3);line('DRAFT • AI-assisted • MathDB 339235',left,25);line(str(pn),W-55,H-25)
 for block in page.strip().split('\n\n'):
  if block.startswith('[TABLE'):
   table(4 if 'M8' in block else 6,edge='EDGES' in block);continue
  bold=block.startswith('#');size=17 if block.startswith('# ') else 12.5 if block.startswith('## ') else 10.5
  s=block.lstrip('# ').strip() if bold else block
  for t in wrap(s,size,bold):line(t,left,y);y+=size*1.23
  y+=7 if bold else 6
 assert y<H-43,(pn,y)
 receipt.append({'page':pn,'last_baseline':round(y,2),'bottom_limit':round(H-43,2)})
 ctx.show_page()
surface.finish();(D/'layout-check.json').write_text(json.dumps(receipt,indent=2));print(receipt)
