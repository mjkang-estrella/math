from pathlib import Path
import json,hashlib,html
import cairo,gi
gi.require_version('Pango','1.0'); gi.require_version('PangoCairo','1.0')
from gi.repository import Pango,PangoCairo
D=Path.cwd(); pages=(D/'paper.md').read_text().split('---PAGE---')
surface=cairo.PDFSurface(str(D/'paper.pdf'),612,792); surface.set_metadata(cairo.PDF_METADATA_TITLE,'Equitable partitions of finite rectangular grids are symmetry orbits'); surface.set_metadata(cairo.PDF_METADATA_AUTHOR,'AI-assisted draft; no human author asserted')
ctx=cairo.Context(surface); bounds=[]
def block(text,x,y,w,size=11.1,bold=False,family='Liberation Serif'):
 l=PangoCairo.create_layout(ctx); fd=Pango.FontDescription(family); fd.set_absolute_size(size*Pango.SCALE); fd.set_weight(Pango.Weight.BOLD if bold else Pango.Weight.NORMAL); l.set_font_description(fd); l.set_width(int(w*Pango.SCALE)); l.set_wrap(Pango.WrapMode.WORD_CHAR); l.set_spacing(int(2.0*Pango.SCALE)); l.set_text(text,-1); ctx.move_to(x,y); PangoCairo.show_layout(ctx,l); return l.get_size()[1]/Pango.SCALE
for i,page in enumerate(pages,1):
 ctx.set_source_rgb(.12,.16,.2); block('MATHDB 343536  /  REVIEW DRAFT',52,29,508,8.2,True,'Liberation Sans'); ctx.set_source_rgb(.65,.7,.73); ctx.set_line_width(.5); ctx.move_to(52,46); ctx.line_to(560,46); ctx.stroke(); ctx.set_source_rgb(.08,.08,.08)
 y=59
 for para in page.strip().split('\n\n'):
  if para.startswith('# '): y+=block(para[2:],52,y,508,20,True)+10
  elif para.startswith('## '): y+=block(para[3:],52,y,508,14,True)+9
  elif ' | ' in para and not para.startswith('TABLE:'):
   cells=para.split(' | '); widths=[44,277,187]; heights=[]; xx=52
   for c,w in zip(cells,widths): heights.append(block(c.strip(),xx+4,y+4,w-8,9.9,para.startswith('Round'))); xx+=w
   hh=max(heights)+8; ctx.set_source_rgb(.7,.7,.7); ctx.move_to(52,y+hh); ctx.line_to(560,y+hh); ctx.stroke(); ctx.set_source_rgb(.08,.08,.08); y+=hh+2
  elif para.startswith('TABLE:'):
   lines=para.split('\n')[1:]
   for j,line in enumerate(lines):
    cols=line.split('|'); xx=52
    for c,w in zip(cols,[230,139,139]): block(c.strip(),xx+5,y+3,w-10,10.3,j==0); xx+=w
    y+=18
   y+=6
  else: y+=block(para.replace('\n',' '),52,y,508,10.0 if para.startswith('[') else 11.1)+8
 assert y<744,(i,y)
 bounds.append({'page':i,'body_bottom_pt':y,'body_limit_pt':744})
 ctx.set_source_rgb(.3,.3,.3); block('Draft • AI-assisted • Zero accepted credit',52,759,470,8.2,False,'Liberation Sans'); block(str(i),540,759,20,8.2,False,'Liberation Sans'); ctx.show_page()
surface.finish(); (D/'receipts/layout.json').write_text(json.dumps({'pages':len(pages),'font':'Liberation Serif 11.1 pt; system Pango fallback for math','bounds':bounds},indent=2)+'\n'); print(bounds)
