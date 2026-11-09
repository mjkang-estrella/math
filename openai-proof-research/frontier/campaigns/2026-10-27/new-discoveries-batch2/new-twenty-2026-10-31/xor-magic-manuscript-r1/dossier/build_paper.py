from pathlib import Path
import json,re,html,sys
sys.path.insert(0,str(Path(__file__).resolve().parent/"local-deps"))
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,XPreformatted,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
R=Path(__file__).resolve().parent
for name,file in [('Body','liberation-serif-fonts/LiberationSerif-Regular.ttf'),('Bold','liberation-serif-fonts/LiberationSerif-Bold.ttf'),('Mono','liberation-mono-fonts/LiberationMono-Regular.ttf'),('Math','google-noto/NotoSansMath-Regular.ttf'),('Symbols','gdouros-symbola/Symbola.ttf')]:
 pdfmetrics.registerFont(TTFont(name,'/usr/share/fonts/'+file))
def esc(s,base='Body'):
 out=''
 for c in s:
  if c in '\n\t' or ord(c) in pdfmetrics.getFont(base).face.charToGlyph: out+=html.escape(c)
  else:
   n=next((n for n in ['Math','Symbols'] if c in '\n\t' or ord(c) in pdfmetrics.getFont(n).face.charToGlyph),None)
   if n is None: raise ValueError('missing glyph '+repr(c))
   out+='<font name="'+n+'">'+html.escape(c)+'</font>'
 return out
s=(R/'manuscript.md').read_text();s=re.sub(r'(?m)^(#{1,2} [^\n]+)\n(?!\n)',r'\1\n\n',s); bases=json.loads((R/'dossier/base-data.json').read_text());seed=[]
for name in ['Base16Closed4','Base16Open5','Base32Closed4','Base32Open5']:
 seed.append('    '+name+':')
 arr=bases[name]['masks_hex']
 seed.extend('    '+','.join(arr[i:i+8]) for i in range(0,len(arr),8))
s=s.replace('{{SEED_DATA}}','\n'.join(seed))
literal=(R/'dossier/formal/Literal.lean').read_text()
blocks=[]
for name in ['OpenMagic','ClosedMagic','OpenExists','ClosedExists','PrintedAt','CorrectedAt']:
 start=literal.index('def '+name+' '); end=literal.index('\n\n',start)
 blocks.append(literal[start:end])
s=s.replace('{{LITERAL_DEFS}}','\n\n'.join('    '+line for line in '\n\n'.join(blocks).splitlines()))
rows=[['Paper statement','Lean declaration (namespace prefix XorMagic unless shown)'],['Total sum; complement identity','total_bits; complement_identity'],['Literal graph definitions','Literal: OpenMagic, ClosedMagic, OpenExists, ClosedExists'],['Seed and orientation','ColouredSeed; FactorColouring; chosen_outgoing'],['Translation choice (Section 3)','translation_exists; TranslationFour module'],['Component fibre argument','EdgeTransport.fibre_transport; fibre_card_reachable;\nsection_of_singleton; section_of_three; connected_of_affine_loop'],['Matching/cycle/color persistence','persistedCycle; ColourPersistence, ComplementDecomposition'],['Interpolation and intervals','InterpAssembly, InterpEndpoints, InterpolationArithmetic'],['Direct finite bases','Base*.connected; corrected_at_4; corrected_at_5'],['Two induction bases','seeds_all; main_ranges'],['Theorem 1','corrected_all : ∀ n : ℕ, 4 ≤ n → CorrectedAt n'],['Theorem 2','not_printed_each_ge_four : ∀ n : ℕ, 4 ≤ n → ¬ PrintedAt n'],['Universal printed negations','printed_not_all; printed_not_positive']]
s=s.replace('{{CORRESPONDENCE}}','\n'.join(' | '.join(r) for r in rows))
(R/'paper-source.md').write_text(s)
# Formal names above are checked against declarations, not inferred from file names.
body=ParagraphStyle('body',fontName='Body',fontSize=9.5,leading=13,spaceAfter=8)
head=ParagraphStyle('head',fontName='Bold',fontSize=13,leading=17,spaceAfter=13)
title=ParagraphStyle('title',parent=head,fontSize=19,leading=24,spaceAfter=16)
mono=ParagraphStyle('mono',fontName='Mono',fontSize=7.05,leading=10,spaceAfter=7)
small=ParagraphStyle('small',parent=body,fontSize=8,leading=11)
story=[]
for pi,page in enumerate(s.split('<!-- PAGE -->')):
 if pi:story.append(PageBreak())
 for para in page.strip().split('\n\n'):
  if not para.strip():continue
  if para.startswith('    '):
   story.append(XPreformatted(esc('\n'.join(x[4:] if x.startswith('    ') else x for x in para.splitlines()),'Mono'),mono))
  elif 'Paper statement | Lean declaration' in para:
   r=[]
   for line in para.splitlines():
    # Continuation in source table is joined into the preceding cell.
    if ' | ' not in line:
     r[-1][1]+=' '+line;continue
    r.append(line.split(' | ',1))
   t=Table([[Paragraph(esc(c),small) for c in row] for row in r],colWidths=[155,337],hAlign='LEFT')
   t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e9eef2')),('LINEBELOW',(0,0),(-1,0),.5,colors.grey),('BOTTOMPADDING',(0,0),(-1,-1),5),('TOPPADDING',(0,0),(-1,-1),4)]));story.append(t);story.append(Spacer(1,10))
  else:
   st=title if para.startswith('# ') else head if para.startswith('## ') else body
   txt=re.sub(r'^#+ ','',para).replace('\n',' ')
   story.append(Paragraph(esc(txt),st))
def footer(c,d):
 c.setTitle('All corrected odd-open and even-closed XOR-magic degrees at powers of two')
 c.setAuthor('Codex research agent (AI-assisted draft; no human author asserted)')
 c.setSubject('MathDB 372205; corrected Conjecture 25; unaccepted draft, zero credit')
 c.setFont('Body',8);c.setFillColor(colors.HexColor('#53616b'))
 c.drawString(54,31,'DRAFT • MathDB 372205 • AI-assisted • No priority claim')
 c.drawRightString(558,31,str(d.page))
doc=SimpleDocTemplate(str(R/'xor-magic-draft.pdf'),pagesize=(612,792),rightMargin=54,leftMargin=54,topMargin=45,bottomMargin=49)
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('PDF built')
