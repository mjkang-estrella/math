from pathlib import Path
import json,html,re
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Table,TableStyle,PageBreak
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
O=Path(__file__).resolve().parent
for name,file in [('Body','DejaVuSerif.ttf'),('Bold','DejaVuSerif-Bold.ttf'),('Sans','DejaVuSans.ttf')]:pdfmetrics.registerFont(TTFont(name,'/home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/libreoffice-headless/libreoffice/share/fonts/truetype/'+file))
styles={0:ParagraphStyle('p',fontName='Body',fontSize=9.2,leading=12.5,spaceAfter=7),1:ParagraphStyle('h1',fontName='Bold',fontSize=21,leading=25,spaceAfter=12),2:ParagraphStyle('h2',fontName='Bold',fontSize=12,leading=16,spaceAfter=10),3:ParagraphStyle('h3',fontName='Bold',fontSize=11,leading=15,spaceAfter=8)}
d=json.loads((O/'evidence/discovery/outputs/pmd-certificate.json').read_text());checks=json.loads((O/'receipts/arithmetic.json').read_text())
def table(rows,widths=None,size=8.3):
 t=Table([[Paragraph(html.escape(str(c)),ParagraphStyle('cell',fontName='Sans',fontSize=size,leading=size+3)) for c in row] for row in rows],colWidths=widths,hAlign='LEFT')
 t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e6edf3')),('VALIGN',(0,0),(-1,-1),'TOP'),('LINEBELOW',(0,0),(-1,0),.5,colors.HexColor('#567')),('BOTTOMPADDING',(0,0),(-1,-1),4),('TOPPADDING',(0,0),(-1,-1),4),('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white,colors.HexColor('#f6f8fa')])]))
 return t
parts=[['Stage','Matching']]+[[i+1,';  '.join('{'+f'{u}, {v}'+'}' for u,v in p)] for i,p in enumerate(d['layers'])]
w=[['i']+list(range(12))]+[[i+1]+a for i,a in enumerate(d['weights'])]
s=[['Edge']+[f'Stage {i}' for i in range(1,6)]]
for u,v in d['edges']:s.append([f'{u}, {v}']+[x['sums'].get(f'{u}-{v}','-') for x in checks[0]['stages']])
e=[['(m,n)','Vertices / edges','Part sizes','Max other residual sum¹']]
for a in checks[1:]:e.append([f"({a['m']},{a['n']})",f"{a['vertices']} / {a['edges']}",', '.join(str(t['matching_size']) for t in a['stages']),', '.join(str(t['other_max']) if t['other_max'] is not None else '-' for t in a['stages'])])
objects={'{{PARTS}}':table(parts,[46,454]),'{{WEIGHTS}}':table(w,[20]+[40]*12,size=7.5),'{{SUMS}}':table(s,[85]+[83]*5,size=7.5),'{{EXTRAS}}':table(e,[50,95,120,235],size=8)}
objects['{{SUMS}}'].setStyle(TableStyle([('BOTTOMPADDING',(0,0),(-1,-1),2),('TOPPADDING',(0,0),(-1,-1),2)]))
text=(O/'paper.md').read_text();story=[]
expanded=text
for token, rows in [('{{PARTS}}',parts),('{{WEIGHTS}}',w),('{{SUMS}}',s),('{{EXTRAS}}',e)]:
 md='\n'.join('| '+' | '.join(map(str,row))+' |' for row in [rows[0],['---']*len(rows[0])]+rows[1:])
 expanded=expanded.replace(token,md)
(O/'paper-source.md').write_text(expanded)
(O/'PROOF.md').write_text('# Proof dossier: MathDB 366974\n\nThe complete self-contained proof and exact arithmetic follow. The lower bound is proved in prose; the supplied Lean endpoint certifies the upper bound and full refutation. Zero accepted credit.\n\n'+expanded)
for block in text.split('\n\n'):
 block=block.strip()
 if not block:continue
 if block=='---PAGE---':story.append(PageBreak());continue
 if block in objects:
  story.extend([objects[block],Spacer(1,9)])
  if block=='{{EXTRAS}}':story.append(Paragraph('¹ The last residual graph is the selected matching itself; the dash denotes an empty set of other edges.',styles[0]))
  continue
 m=re.match(r'^(#{1,3}) (.*)',block,re.S)
 level=len(m[1]) if m else 0;body=m[2] if m else block
 # Wrap hash strings at the midpoint, without changing source bytes.
 if re.fullmatch('[0-9a-f]{64}',body):body=body[:32]+' '+body[32:]
 escaped=html.escape(body).replace('\n',' ')
 for char in set(body):
  if ord(char)>127 and ord(char) not in pdfmetrics.getFont('Body' if level==0 else 'Bold').face.charToGlyph:
   escaped=escaped.replace(char, '<font name="Sans">'+char+'</font>')
 story.append(Paragraph(escaped,styles[level]))
def footer(c,doc):
 c.setFont('Sans',7);c.setFillColor(colors.HexColor('#526477'));c.drawString(47,27,'DRAFT • AI-assisted • MathDB 366974 • No acceptance credit');c.drawRightString(565,27,str(doc.page))
doc=SimpleDocTemplate(str(O/'paper.pdf'),pagesize=(612,792),rightMargin=47,leftMargin=47,topMargin=39,bottomMargin=43,title='Five positive matchings for C3 square C4',author='AI-assisted draft; no human authorship asserted')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('Built paper.pdf')
