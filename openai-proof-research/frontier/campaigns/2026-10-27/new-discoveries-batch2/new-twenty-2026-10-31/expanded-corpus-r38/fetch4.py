exec(open(__file__.replace('fetch4.py','fetch.py')).read().split('items=')[0])
items=[('current-preprints','https://api.github.com/repos/OpenAI/math/git/trees/3f56f68a176b4494c346091ea0a319651bc217ec?recursive=1'),('omega-popclassification-body','https://raw.githubusercontent.com/the-omega-institute/trureturing/83d511b2495f30ac194415b446456e054419be22/D5/S3/Combinatorics/PopStack/PopStackClassification.lean')]
exec(open(__file__.replace('fetch4.py','fetch.py')).read().split('receipts=[]')[1].join(['receipts=[]','']).replace("H/'fetch-receipts.json'","H/'fetch4-receipts.json'"))
