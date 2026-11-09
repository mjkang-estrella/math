from run import *
import xml.etree.ElementTree as E,re
p=L/'primary/older.xml';a=sha(p);r=E.fromstring(p.read_bytes());assert sha(p)==a
hist=json.loads((L/'history-index.json').read_text())
out=[]
for e in r.findall('{*}entry'):
 id=e.find('{*}id').text.split('/abs/')[1];title=e.find('{*}title').text
 terms=[id.split('v')[0],title[:45]]
 hits=[x['path'] for x in hist if any(t.lower() in x['text'].lower() for t in terms)]
 out.append({'id':id,'title':title,'history_hits':hits})
 print(id,title,'DUP',len(hits))
dump('dedup-selection.json',out)
# Replace historical report copies by compact immutable references.
dump('history-index.json',[{'path':x['path'],'sha256':x['sha256']} for x in hist])
