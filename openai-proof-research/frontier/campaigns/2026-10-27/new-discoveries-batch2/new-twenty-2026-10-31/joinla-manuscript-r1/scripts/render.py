"""Build editable Flat ODF with standard-library XML; export with LibreOffice."""
from pathlib import Path
import json,re,html,xml.etree.ElementTree as ET
p=Path(__file__).resolve().parent.parent
pages=json.loads((p/'paper-content.json').read_text())
ns={'office':'urn:oasis:names:tc:opendocument:xmlns:office:1.0','style':'urn:oasis:names:tc:opendocument:xmlns:style:1.0','text':'urn:oasis:names:tc:opendocument:xmlns:text:1.0','fo':'urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0','table':'urn:oasis:names:tc:opendocument:xmlns:table:1.0','svg':'urn:oasis:names:tc:opendocument:xmlns:svg-compatible:1.0'}
for k,v in ns.items():ET.register_namespace(k,v)
def el(parent,tag,attrs=None,text=None):
 def q(s):a,b=s.split(':');return '{'+ns[a]+'}'+b
 e=ET.SubElement(parent,q(tag),{q(k):v for k,v in (attrs or {}).items()})
 e.text=text;return e
root=ET.Element('{'+ns['office']+'}document',{'{'+ns['office']+'}version':'1.3','{'+ns['office']+'}mimetype':'application/vnd.oasis.opendocument.text'})
styles=el(root,'office:styles')
for name,size,font in [('Body','10pt','Liberation Serif'),('Title','16pt','Liberation Serif'),('Eq','10pt','Noto Sans Math'),('Hash','7.8pt','Liberation Mono'),('Cell','10pt','Liberation Mono'),('Footer','8pt','Liberation Sans')]:
 s=el(styles,'style:style',{'style:name':name,'style:family':'paragraph'})
 el(s,'style:paragraph-properties',{'fo:margin-bottom':'0.085in','fo:line-height':'126%','fo:text-align':'center' if name in ['Eq','Cell'] else 'left'})
 el(s,'style:text-properties',{'fo:font-size':size,'fo:font-family':font,**({'fo:font-weight':'bold'} if name=='Title' else {})})
s=el(styles,'style:style',{'style:name':'TitleBreak','style:family':'paragraph','style:parent-style-name':'Title'});el(s,'style:paragraph-properties',{'fo:break-before':'page'})
for name,attrs in [('Bold',{'fo:font-weight':'bold'}),('Italic',{'fo:font-style':'italic'}),('Sub',{'style:text-position':'sub 75%'})]:
 s=el(styles,'style:style',{'style:name':name,'style:family':'text'});el(s,'style:text-properties',attrs)
auto=el(root,'office:automatic-styles');layout=el(auto,'style:page-layout',{'style:name':'Page'})
el(layout,'style:page-layout-properties',{'fo:page-width':'8.5in','fo:page-height':'11in','fo:margin-left':'0.75in','fo:margin-right':'0.75in','fo:margin-top':'0.65in','fo:margin-bottom':'0.65in'})
t=el(auto,'style:style',{'style:name':'Table','style:family':'table'});el(t,'style:table-properties',{'style:width':'6.8in','table:align':'center','fo:margin-bottom':'0.12in'})
t=el(auto,'style:style',{'style:name':'Col','style:family':'table-column'});el(t,'style:table-column-properties',{'style:column-width':'0.97in'})
t=el(auto,'style:style',{'style:name':'Box','style:family':'table-cell'});el(t,'style:table-cell-properties',{'fo:padding':'0.06in','fo:border-bottom':'0.4pt solid #708090'})
masters=el(root,'office:master-styles');master=el(masters,'style:master-page',{'style:name':'Standard','style:page-layout-name':'Page'})
footer=el(master,'style:footer');f=el(footer,'text:p',{'text:style-name':'Footer'},'DRAFT · AI-assisted · MathDB 365453 · zero accepted credit | page ');el(f,'text:page-number',{'text:select-page':'current'},'1')
body=el(root,'office:body');text=el(body,'office:text');md=[]
for i,page in enumerate(pages):
 el(text,'text:p',{'text:style-name':'TitleBreak' if i else 'Title'},page['title']);md.append('# '+page['title']+'\n')
 for kind,s in page['blocks']:
  if kind=='table':
   for row in s:
    line=''.join(str(v).rjust(8) for v in row)
    par=el(text,'text:p',{'text:style-name':'Cell'})
    parts=re.split('( +)',line)
    for part in parts:
     if not part:continue
     if part.isspace():el(par,'text:s',{'text:c':str(len(part))})
     else:el(par,'text:span',{},part)
   md.append('\n'.join('| '+' | '.join(map(str,r))+' |' for r in s)+'\n');continue
  par=el(text,'text:p',{'text:style-name':{'p':'Body','eq':'Eq','hash':'Hash'}[kind]})
  node=ET.fromstring('<r>'+s.replace('<br/>','<br/>')+'</r>')
  par.text=node.text
  for child in node:
   if child.tag=='br':e=el(par,'text:line-break')
   else:e=el(par,'text:span',{'text:style-name':{'b':'Bold','i':'Italic','sub':'Sub'}[child.tag]},child.text)
   e.tail=child.tail
  md.append(re.sub('<[^>]*>','',html.unescape(s))+'\n')
ET.ElementTree(root).write(p/'paper.fodt',encoding='utf-8',xml_declaration=True)
(p/'paper.md').write_text('\n'.join(md))
a=next(i for i,s in enumerate(md) if s.startswith('# The complete'));b=next(i for i,s in enumerate(md) if s.startswith('# Literal'))
(p/'PROOF.md').write_text('# Complete proof and supporting certificate\n\n'+'\n'.join(md[a:b]))
print('Created paper.fodt and readable sources')
