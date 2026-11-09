from pathlib import Path
import json,html,re,xml.etree.ElementTree as E
R=Path.cwd()
ns={'office':'urn:oasis:names:tc:opendocument:xmlns:office:1.0','text':'urn:oasis:names:tc:opendocument:xmlns:text:1.0','style':'urn:oasis:names:tc:opendocument:xmlns:style:1.0','fo':'urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0','table':'urn:oasis:names:tc:opendocument:xmlns:table:1.0','svg':'urn:oasis:names:tc:opendocument:xmlns:svg-compatible:1.0'}
for k,v in ns.items(): E.register_namespace(k,v)
def q(s): a,b=s.split(':'); return '{'+ns[a]+'}'+b
def add(p,tag,attrs={},text=None):
 e=E.SubElement(p,q(tag),{q(k):v for k,v in attrs.items()}); e.text=text; return e
root=E.Element(q('office:document'),{q('office:version'):'1.3',q('office:mimetype'):'application/vnd.oasis.opendocument.text'})
styles=add(root,'office:styles')
for name,size,weight,spacing in [('Body','10.5pt','normal','0.075in'),('Compact','10pt','normal','0.065in'),('TableText','9.1pt','normal','0.015in'),('Small','9.1pt','normal','0.055in'),('Heading','13pt','bold','0.12in'),('Title','20pt','bold','0.14in'),('Quote','9.1pt','normal','0.075in')]:
 s=add(styles,'style:style',{'style:name':name,'style:family':'paragraph'})
 add(s,'style:text-properties',{'fo:font-family':'Liberation Serif','fo:font-size':size,'fo:font-weight':weight})
 add(s,'style:paragraph-properties',{'fo:margin-bottom':spacing,'fo:line-height':'124%','fo:keep-together':'always',**({'fo:keep-with-next':'always'} if name in ['Title','Heading'] else {})})
for name,props in [('bold',{'fo:font-weight':'bold'}),('italic',{'fo:font-style':'italic'}),('sub',{'style:text-position':'sub 75%'})]:
 s=add(styles,'style:style',{'style:name':name,'style:family':'text'}); add(s,'style:text-properties',props)
auto=add(root,'office:automatic-styles')
s=add(auto,'style:style',{'style:name':'NewHeading','style:family':'paragraph','style:parent-style-name':'Heading'}); add(s,'style:paragraph-properties',{'fo:break-before':'page'})
pl=add(auto,'style:page-layout',{'style:name':'Page'}); add(pl,'style:page-layout-properties',{'fo:page-width':'8.5in','fo:page-height':'11in','fo:margin-left':'0.75in','fo:margin-right':'0.75in','fo:margin-top':'0.62in','fo:margin-bottom':'0.62in'})
masters=add(root,'office:master-styles'); master=add(masters,'style:master-page',{'style:name':'Standard','style:page-layout-name':'Page'})
f=add(master,'style:footer'); p=add(f,'text:p',{'text:style-name':'Small'},'DRAFT · AI-assisted · Orientable total domination                                      '); add(p,'text:page-number',{'text:select-page':'current'},'1')
body=add(add(root,'office:body'),'office:text')
def para(text,style):
 p=add(body,'text:p',{'text:style-name':style})
 frag=E.fromstring('<x>'+text+'</x>'); p.text=frag.text
 def copy(parent,el):
  span=add(parent,'text:span',{'text:style-name':{'b':'bold','i':'italic','sub':'sub'}[el.tag]}); span.text=el.text; span.tail=el.tail
  for child in el: copy(span,child)
 for el in frag: copy(p,el)
qual=json.loads((R/'inputs/orientdom-root-ruling-r2.json').read_text())['gate_D_ruling']
ver=json.loads((R/'recomputed/verification.json').read_text())
formal=[('Rel / Arc','Boolean adjacency / equality to true.'),('Valid','Every vertex has an incoming arc.'),('Asym','No opposite arcs, hence no loops.'),('Same','Identical underlying undirected support.'),('OrientationOf G D','Asym D and support exactly G.'),('TD D S','Every vertex has an in-neighbour in S.'),('Minimum D S','TD D S and |S| ≤ |T| for every TD set T.'),('spectrum G','Attained minimum sizes, within 0,…,|V|.'),('lower / upper','Actual min′ and max′ of nonempty spectrum.'),('Conjecture','All intermediate sizes belong to spectrum.'),('conjecture_true','A proof of this literal Conjecture.')]
def table(rows):
 t=add(body,'table:table'); add(t,'table:table-column',{'table:number-columns-repeated':str(len(rows[0]))})
 for row in rows:
  tr=add(t,'table:table-row')
  for cell in row:
   tc=add(tr,'table:table-cell'); add(tc,'text:p',{'text:style-name':'TableText'},cell)
for i,page in enumerate((R/'paper.md').read_text().split('---PAGE---')):
 for j,block in enumerate(page.strip().split('\n\n')):
  if block=='[[ROOT_QUALIFICATIONS]]':
   for s in qual: para(html.escape(s),'Quote')
  elif block=='[[ENUM_TABLE]]':
   table([['Order','Admissible graphs','Valid orientations','Gaps']]+[[str(d['n']),f"{d['graphs']:,}",f"{d['orientations']:,}",str(d['gaps'])] for d in ver['orders']])
  elif block=='[[FORMAL_TABLE]]': table(formal)
  else:
   st='Small' if i==4 else ('Compact' if i==3 else 'Body')
   if block.startswith('# '): block=block[2:]; st='Title'
   elif block.startswith('## '): block=block[3:]; st='NewHeading' if i>0 and j==0 else 'Heading'
   para(block,st)
E.ElementTree(root).write(R/'paper.fodt',encoding='utf-8',xml_declaration=True)
print('Built paper.fodt')
