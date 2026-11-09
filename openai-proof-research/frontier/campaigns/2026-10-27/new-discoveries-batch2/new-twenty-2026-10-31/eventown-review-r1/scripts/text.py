from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0;self.math=0
 def handle_starttag(self,t,a):
  if t in ("script","style"):self.skip+=1
  if t=="math":self.math+=1;self.out.append(dict(a).get("alttext",""))
 def handle_endtag(self,t):
  if t in ("script","style"):self.skip-=1
  if t=="math":self.math-=1
 def handle_data(self,d):
  if not self.skip and not self.math:self.out.append(d)
import pathlib,re,json
for p in pathlib.Path('receipts').glob('*.body'):
 if p.name.endswith('HEAD.body'):
  d=json.loads(p.read_text());s={'sha':d['sha'],'date':d['commit']['committer']['date'],'message':d['commit']['message'],'files_truncated_possible':len(d.get('files',[]))>=300,'file_count':len(d.get('files',[])),'matched_files':[f['filename'] for f in d.get('files',[]) if re.search(r'eventown|372630|372631|lindzey|singular',f['filename'],re.I)]};pathlib.Path('outputs/'+p.stem+'.json').write_text(json.dumps(s,indent=2));print(s);continue
 parser=Parser();parser.feed(p.read_text());text=' '.join(' '.join(parser.out).split());pathlib.Path('outputs/'+p.stem+'.txt').write_text(text)
 print('\n',p.name,'START',text[:500])
 pattern=r'precisely|Conjecture 16|Conjecture 17|Submission history|8\^|Füredi|reversing|12613|even-cycle|singular|Lindzey'
 matches=list(re.finditer(pattern,text,re.I));print('\n'.join(text[max(0,m.start()-150):m.end()+350] for m in matches[:30]))
