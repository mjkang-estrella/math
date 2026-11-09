from pathlib import Path
from xml.sax.saxutils import escape
r=Path(__file__).resolve().parent.parent
parts=[]
for pi,page in enumerate((r/'paper.md').read_text().split('===PAGE===')):
 for j,block in enumerate(page.strip().split('\n\n')):
  style='Body'
  if block.startswith('# '): style='Title'; block=block[2:]
  elif block.startswith('## '): style='Heading'; block=block[3:]
  if j==0 and pi: style='PageHeading'
  if block=='FORMAL_TABLE':
   rows=[('Source / claim','Formal object or endpoint'),('Definitions 1.2, 1.3','IsOCD / IsOCD\'; middle'),('Connected graph on 8 vertices','G8_connected'),('Attained minimum for G8, A / B',"g8_value / g8_value'"),('Attained minimum for M(G8), A / B',"middle_g8_value / middle_g8_value'"),('Connected universal refutation, A / B',"mathdb_355217_connected /\nmathdb_355217_connected'")]
   s='<table:table table:name="Correspondence" table:style-name="Table"><table:table-column table:style-name="Col"/><table:table-column table:style-name="Col"/>'
   for row in rows:
    s+='<table:table-row>'+''.join('<table:table-cell><text:p text:style-name="TableText">'+escape(v).replace('\n','<text:line-break/>')+'</text:p></table:table-cell>' for v in row)+'</table:table-row>'
   parts.append(s+'</table:table>'); continue
  parts.append('<text:p text:style-name="'+style+'">'+escape(block)+'</text:p>')
xml='''<?xml version="1.0" encoding="UTF-8"?>
<office:document xmlns:office="urn:oasis:names:tc:opendocument:xmlns:office:1.0" xmlns:style="urn:oasis:names:tc:opendocument:xmlns:style:1.0" xmlns:text="urn:oasis:names:tc:opendocument:xmlns:text:1.0" xmlns:table="urn:oasis:names:tc:opendocument:xmlns:table:1.0" xmlns:fo="urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0" office:version="1.3" office:mimetype="application/vnd.oasis.opendocument.text">
<office:styles>
<style:default-style style:family="paragraph"><style:paragraph-properties fo:line-height="118%" fo:margin-bottom="0.10in"/><style:text-properties style:font-name="Noto Serif" fo:font-family="Noto Serif" fo:font-size="10pt"/></style:default-style>
<style:style style:name="Body" style:family="paragraph"><style:paragraph-properties fo:text-align="start"/></style:style>
<style:style style:name="Title" style:family="paragraph"><style:paragraph-properties fo:margin-bottom="0.16in"/><style:text-properties fo:font-size="17pt" fo:font-weight="bold"/></style:style>
<style:style style:name="Heading" style:family="paragraph"><style:paragraph-properties fo:margin-top="0.10in" fo:margin-bottom="0.12in" fo:keep-with-next="always"/><style:text-properties fo:font-size="12pt" fo:font-weight="bold"/></style:style>
<style:style style:name="PageHeading" style:parent-style-name="Heading" style:family="paragraph"><style:paragraph-properties fo:break-before="page"/></style:style>
<style:style style:name="TableText" style:family="paragraph"><style:paragraph-properties fo:margin-bottom="0.04in" fo:line-height="110%"/><style:text-properties fo:font-size="8pt"/></style:style>
</office:styles>
<office:automatic-styles><style:page-layout style:name="Page"><style:page-layout-properties fo:page-width="8.5in" fo:page-height="11in" fo:margin-top="0.65in" fo:margin-bottom="0.65in" fo:margin-left="0.72in" fo:margin-right="0.72in"/><style:footer-style><style:header-footer-properties fo:min-height="0.2in"/></style:footer-style></style:page-layout><style:style style:name="Table" style:family="table"><style:table-properties style:width="7in"/></style:style><style:style style:name="Col" style:family="table-column"><style:table-column-properties style:column-width="3.5in"/></style:style></office:automatic-styles>
<office:master-styles><style:master-page style:name="Standard" style:page-layout-name="Page"><style:footer><text:p text:style-name="TableText">DRAFT • AI-assisted • MathDB 355217 • zero accepted credit | Page <text:page-number/></text:p></style:footer></style:master-page></office:master-styles>
<office:body><office:text>'''+''.join(parts)+'''</office:text></office:body></office:document>'''
(r/'paper.fodt').write_text(xml)
