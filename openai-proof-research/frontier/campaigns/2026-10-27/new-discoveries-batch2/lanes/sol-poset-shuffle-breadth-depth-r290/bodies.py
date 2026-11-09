from research import *
import xml.etree.ElementTree as E
queries={'borosmoll':'ti:"Boros" AND ti:"Moll" AND au:Kauers', 'shuffle-spectrum':'ti:"random-to-random" AND au:Saliola','magnitude-successor':'ti:"magnitude" AND au:Barcelo','stanleydepth-successor':'ti:"non-partitionable"','delta-successor':'ti:"Delta conjecture" AND au:DAdderio','bunkbed-successor':'ti:"bunkbed" AND au:Pak','shannon-successor':'ti:"Shannon capacity" AND all:"disjoint union"'}
for k,q in queries.items():fetch(k+'.atom','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=5&sortBy=submittedDate&sortOrder=ascending')
ids=['0908.1582v2','0811.0949v2','0712.2308v1','1509.07058v4','math/0408312v2','cs/0608021v1','1008.4707v1']
patterns=ids+['Boros','magnitude','bunkbed','Neggers','Stanley depth','Delta Conjecture','Shannon capacity','Fon-der-Flaass']
r=subprocess.run(['rg','-il','--glob','*.md','--glob','!AGENTS.md','--glob','!**/administrative/**','--glob','!**/history/**','--glob','!**/frozen/**','|'.join(patterns),str(L.parent)],capture_output=True,text=True)
lines=[x for x in r.stdout.splitlines() if str(L) not in x];(L/'early-alias-paths.json').write_text(json.dumps(lines,indent=2));print('DEDUP',len(lines),lines[:65])
for id in ids:
 key=id.replace('/','-')+'.pdf';fetch(key,'https://arxiv.org/pdf/'+id)
 if (L/'primary'/key).exists():extract(L/'primary'/key)
