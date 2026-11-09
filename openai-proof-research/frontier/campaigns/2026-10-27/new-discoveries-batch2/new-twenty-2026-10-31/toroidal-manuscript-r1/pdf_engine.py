"""Small offline PDF typesetter: embedded TrueType, Unicode maps, wrapped paragraphs.
No third-party Python dependencies. Only the manuscript's layout primitives are supported.
"""
import struct,re,html, pathlib,zlib
from html.parser import HTMLParser
def u16(b,o):return struct.unpack_from('>H',b,o)[0]
def i16(b,o):return struct.unpack_from('>h',b,o)[0]
class TTFont:
 def __init__(self,name,path):
  self.name=name;self.raw=pathlib.Path(path).read_bytes(); b=self.raw
  self.tables={b[o:o+4].decode():struct.unpack_from('>II',b,o+8) for o in range(12,12+16*u16(b,4),16)}
  def tab(n):o,l=self.tables[n];return b[o:o+l]
  head=tab('head');self.units=u16(head,18);self.box=[i16(head,o) for o in (36,38,40,42)]
  hhea=tab('hhea');self.asc=i16(hhea,4);self.desc=i16(hhea,6);n=u16(hhea,34)
  hm=tab('hmtx');self.widths=[u16(hm,4*i) for i in range(n)]
  cm=tab('cmap');self.cmap={}
  for k in range(u16(cm,2)):
   off=struct.unpack_from('>I',cm,4+8*k+4)[0]
   if u16(cm,off)!=4:continue
   c=cm[off:];count=u16(c,6)//2
   for j in range(count):
    end=u16(c,14+2*j);start=u16(c,16+2*count+2*j);delta=i16(c,16+4*count+2*j);ri=16+6*count+2*j;ro=u16(c,ri)
    for code in range(start,min(end+1,65535)):
     gid=(code+delta)&65535 if ro==0 else u16(c,ri+ro+2*(code-start))
     if ro and gid:gid=(gid+delta)&65535
     if gid:self.cmap[code]=gid
  self.used={};self.tag=''
 def width(self,t,size):
  total=0
  for c in t:
   assert ord(c) in self.cmap,('font missing',c,hex(ord(c)))
   gid=self.cmap[ord(c)];total+=self.widths[min(gid,len(self.widths)-1)]
  return total*size/self.units
 def encode(self,t):
  for c in t:
   if ord(c) not in self.used:self.used[ord(c)]=len(self.used)+1
  return ''.join(f'{self.used[ord(c)]:04x}' for c in t)
class Metrics:
 def __init__(self):self.fonts={}
 def registerFont(self,f):self.fonts[f.name]=f
 def registerFontFamily(self,*a,**kw):pass
pdfmetrics=Metrics()
class Colors:
 def HexColor(self,s):return tuple(int(s[i:i+2],16)/255 for i in (1,3,5))
colors=Colors()
class ParagraphStyle:
 def __init__(self,name,parent=None,**kw):
  self.__dict__.update(parent.__dict__ if parent else dict(fontName='Body',fontSize=10,leading=13,spaceAfter=0,spaceBefore=0));self.__dict__.update(kw)
class Parse(HTMLParser):
 def __init__(self):super().__init__();self.spans=[];self.bold=0;self.sub=0
 def handle_starttag(self,t,a):
  if t=='b':self.bold+=1
  if t=='sub':self.sub+=1
 def handle_endtag(self,t):
  if t=='b':self.bold-=1
  if t=='sub':self.sub-=1
 def handle_data(self,s):self.spans.append((s,self.bold,self.sub))
class Paragraph:
 def __init__(self,text,style):self.text=text;self.style=style
 def lines(self,width):
  p=Parse();p.feed(self.text);tokens=[]
  for s,b,sub in p.spans:
   f='Bold' if b else self.style.fontName;size=self.style.fontSize*(.76 if sub else 1)
   tokens.extend((t,f,size,sub) for t in re.findall(r'\s+|\S+',s))
  lines=[];line=[];used=0
  for t,f,sz,sub in tokens:
   if not line:t=t.lstrip()
   if not t:continue
   w=pdfmetrics.fonts[f].width(t,sz)
   if used+w>width and line and t.strip():lines.append(line);line=[];used=0
   if not line and not t.strip():continue
   if w>width: # wrap unusually long identifiers without clipping
    for ch in t:
     cw=pdfmetrics.fonts[f].width(ch,sz)
     if used+cw>width and line:lines.append(line);line=[];used=0
     line.append((ch,f,sz,sub));used+=cw
   else:line.append((t,f,sz,sub));used+=w
  if line:lines.append(line)
  return lines
class Spacer:
 def __init__(self,w,h):self.h=h
class PageBreak:pass
class TableStyle:
 def __init__(self,*a):pass
class Table:
 def __init__(self,data,colWidths,hAlign=None):self.data=data;self.widths=colWidths
 def setStyle(self,s):pass
class PDF:
 def __init__(self):self.objs=[];self.commands=[];self.pagecommands=[];self.font='Body';self.size=10;self.fill=(0,0,0)
 def obj(self,data):
  if isinstance(data,str):data=data.encode()
  self.objs.append(data);return len(self.objs)
 def stream(self,data,extra=''):return self.obj(f'<< /Length {len(data)} {extra} >>\nstream\n'.encode()+data+b'\nendstream')
 def setFont(self,f,s):self.font=f;self.size=s
 def setFillColor(self,c):self.fill=c
 def setStrokeColor(self,c):self.commands.append('%g %g %g RG'%c)
 def line(self,x,y,x2,y2):self.commands.append(f'{x} {y} m {x2} {y2} l S')
 def text(self,x,y,t,f,sz,color=(0,0,0)):
  font=pdfmetrics.fonts[f];encoded=font.encode(t)
  self.commands.append('BT /%s %g Tf %g %g %g rg 1 0 0 1 %g %g Tm <%s> Tj ET'%(font.tag,sz,*color,x,y,encoded))
 def drawString(self,x,y,t):self.text(x,y,t,self.font,self.size,self.fill)
 def drawRightString(self,x,y,t):self.drawString(x-pdfmetrics.fonts[self.font].width(t,self.size),y,t)
 def rect(self,x,y,w,h,color):self.commands.append('%g %g %g rg %g %g %g %g re f'%(*color,x,y,w,h))
 def savepage(self):self.pagecommands.append('\n'.join(self.commands).encode());self.commands=[]
 def write(self,path,title,author):
  catalog=self.obj('');pages=self.obj('');fontrefs={}
  for f in pdfmetrics.fonts.values():
   file=self.stream(zlib.compress(f.raw),f'/Filter /FlateDecode /Length1 {len(f.raw)}')
   scale=1000/f.units
   desc=self.obj(f'<< /Type /FontDescriptor /FontName /{f.name} /Flags 34 /FontBBox [{" ".join(str(int(x*scale)) for x in f.box)}] /ItalicAngle 0 /Ascent {int(f.asc*scale)} /Descent {int(f.desc*scale)} /CapHeight 700 /StemV 80 /FontFile2 {file} 0 R >>')
   n=len(f.used);gids=bytearray(2*(n+1));widths=[];maps=[]
   for cp,cid in f.used.items():
    gid=f.cmap[cp];struct.pack_into('>H',gids,2*cid,gid);widths.append(int(f.widths[min(gid,len(f.widths)-1)]*scale));maps.append(f'<{cid:04X}> <{cp:04X}>')
   gm=self.stream(bytes(gids));cmtext='/CIDInit /ProcSet findresource begin 12 dict begin begincmap /CIDSystemInfo << /Registry (Adobe) /Ordering (UCS) /Supplement 0 >> def /CMapName /Unicode def /CMapType 2 def 1 begincodespacerange <0000> <FFFF> endcodespacerange\n'
   for i in range(0,len(maps),90):chunk=maps[i:i+90];cmtext+=f'{len(chunk)} beginbfchar\n'+'\n'.join(chunk)+'\nendbfchar\n'
   cmtext+='endcmap CMapName currentdict /CMap defineresource pop end end'
   cm=self.stream(cmtext.encode());cf=self.obj(f'<< /Type /Font /Subtype /CIDFontType2 /BaseFont /{f.name} /CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >> /FontDescriptor {desc} 0 R /CIDToGIDMap {gm} 0 R /W [1 [{" ".join(map(str,widths))}]] >>')
   fontrefs[f.tag]=self.obj(f'<< /Type /Font /Subtype /Type0 /BaseFont /{f.name} /Encoding /Identity-H /DescendantFonts [{cf} 0 R] /ToUnicode {cm} 0 R >>')
  pageids=[];fontdict=' '.join(f'/{tag} {ref} 0 R' for tag,ref in fontrefs.items())
  for cmd in self.pagecommands:
   content=self.stream(cmd);pageids.append(self.obj(f'<< /Type /Page /Parent {pages} 0 R /MediaBox [0 0 612 792] /Resources << /Font << {fontdict} >> >> /Contents {content} 0 R >>'))
  self.objs[catalog-1]=f'<< /Type /Catalog /Pages {pages} 0 R >>'.encode();self.objs[pages-1]=f'<< /Type /Pages /Count {len(pageids)} /Kids [{" ".join(str(i)+" 0 R" for i in pageids)}] >>'.encode()
  data=bytearray(b'%PDF-1.7\n%\xe2\xe3\xcf\xd3\n');offsets=[0]
  for i,obj in enumerate(self.objs,1):offsets.append(len(data));data+=f'{i} 0 obj\n'.encode()+obj+b'\nendobj\n'
  start=len(data);data+=f'xref\n0 {len(offsets)}\n0000000000 65535 f \n'.encode()
  for off in offsets[1:]:data+=f'{off:010d} 00000 n \n'.encode()
  data+=f'trailer << /Size {len(offsets)} /Root {catalog} 0 R >>\nstartxref\n{start}\n%%EOF\n'.encode();pathlib.Path(path).write_bytes(data)
class SimpleDocTemplate:
 def __init__(self,path,**kw):self.path=path;self.kw=kw;self.page=1
 def build(self,story,onFirstPage,onLaterPages):
  c=PDF()
  for i,f in enumerate(pdfmetrics.fonts.values()):f.tag=f'F{i}'
  y=749;bottom=53;x=48;width=516;heights=[];start=y
  def drawpara(p,x,y,width):
   for line in p.lines(width):
    xx=x
    for t,f,sz,sub in line:c.text(xx,y-sz*.85-(2 if sub else 0),t,f,sz);xx+=pdfmetrics.fonts[f].width(t,sz)
    y-=p.style.leading
   return y
  for item in story:
   if isinstance(item,PageBreak):
    heights.append(start-y);(onFirstPage if self.page==1 else onLaterPages)(c,self);c.savepage();self.page+=1;y=start;continue
   if isinstance(item,Spacer):y-=item.h
   elif isinstance(item,Paragraph):
    y-=getattr(item.style,'spaceBefore',0);y=drawpara(item,x,y,width)-item.style.spaceAfter
   elif isinstance(item,Table):
    for ri,row in enumerate(item.data):
     h=max(len(p.lines(w-12))*p.style.leading+6 for p,w in zip(row,item.widths))
     if ri==0:c.rect(x,y-h,sum(item.widths),h,(.906,.929,.945))
     xx=x
     for p,w in zip(row,item.widths):drawpara(p,xx+6,y-3,w-12);xx+=w
     y-=h
   assert y>=bottom,('page overflow',self.page,y)
  heights.append(start-y);onLaterPages(c,self);c.savepage();c.write(self.path,self.kw['title'],self.kw['author'])
  assert self.page==6,self.page
  pathlib.Path(self.path).with_suffix('.layout.json').write_text(__import__('json').dumps({'pages':self.page,'content_heights_points':heights,'usable_height_points':696,'font_embedding':'Liberation Serif regular and bold TrueType; Unicode mappings; all glyphs present'},indent=2)+'\n')
