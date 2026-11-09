from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
meta={};reads=[]
for row in R['rows']:
 idx=row['mathdb_id'];p=L/f'abs-{idx}.html'
 if p.exists():
  parser=Text();parser.feed(p.read_text());t=' '.join(parser.parts);chunks=[]
  for pat in ['Submission history','Journal reference','Comments:','Submitted on']:
   j=t.find(pat)
   if j>=0:chunks.append(t[j:j+800])
  meta[str(idx)]={'source_header':(L/f'source-{idx}.txt').read_text()[:1000],'abs_passages':chunks};print(idx,' '.join(chunks)[:1000])
wj('version-journal-inventory.json',meta)
for name in ['leanpool-projects','tauceti-math']:
 t=(L/(name+'.txt')).read_text();paths=list(dict.fromkeys(re.findall(r'"path":"([^"]+)"',t)));print(name,paths);reads.append({'file':name+'.txt','sha256':H(t.encode()),'paths':paths,'depth':'directory names, no descendant body clearance'})
for p in [L.parents[5]/'sources/CONTENTS.md',L/'openai-current-contents.txt']:
 t=p.read_text();terms=['Gaussian','Vinogradov','Singhi','primitive subsets','prime labeling','consumption','Orlik','Z-polynomial','nowhere FO'];hits=[(i+1,l) for i,l in enumerate(t.splitlines()) if any(x.lower() in l.lower() for x in terms)];print('CATALOGUE',str(p),hits);reads.append({'path':str(p),'sha256':H(t.encode()),'literal_terms':terms,'matches':hits,'depth':'full machine text scan, emitted matching lines only; no proof-body clearance'})
wj('registry-and-pinned-screen.json',{'reads':reads,'limitation':'bounded catalogue screen; empty root imports are not complete inventories; no absence claim'})
for name in ['hertling-journal']:
 p=L/(name+'.txt');parser=Text();parser.feed(p.read_text());write(name+'-clean.txt','\n'.join(parser.parts))
