exec(compile(open('investigate.py').read().split("mode=sys.argv[1]")[0],'caps','exec'))
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.txt=[]
 def handle_data(self,s):self.txt.append(s)
rows=[]
for p in sorted((L/'sources').glob('*.abs.html')):
 s=p.read_text();parser=P();parser.feed(s);txt=' '.join(' '.join(parser.txt).split());put('sources/'+p.stem+'.txt',txt)
 tags=dict(re.findall(r'<meta name="([^"]+)" content="([^"]*)"',s));v=re.findall(r'\[v\d+\].{0,180}',txt);rec={'file':p.name,'metadata':{k:v for k,v in tags.items() if k.startswith('citation_')},'versions':v,'submission_history':txt[txt.find('Submission history'):txt.find('Submission history')+1300]};rows.append(rec);print(json.dumps(rec))
js('versions-metadata.json',rows);receipt('metadata',{'true_exit':0})
