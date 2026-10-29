exec(open(__file__.replace('follow.py','fetch.py')).read().split('for name,repo,old in')[0])
rows=json.loads((D/'http-receipts.json').read_text())
j=json.loads((D/'live/omega-delta.json').read_text());h=json.loads((D/'live/omega-head.json').read_text())['sha']
for i,f in enumerate(j['files']):
 if f['filename'].endswith('.md'):get('https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+f['filename'],'omega-body-'+str(i)+'.md')
get('https://www.chierichetti.name/publications','coauthor-publications.html')
get('https://iris.uniroma1.it/cris/rp/rp17102','iris-author.html')
get('https://raw.githubusercontent.com/mirkogiacchini/metricityChatterjeeCoefficient/b0a0c799d4f732d0e193554cd548e46883580ac4/README.md','author-code-readme.md')
get('https://arxiv.org/abs/2505.08045','rockel-abs.html')
get('https://arxiv.org/abs/2606.07354','adapted-abs.html')
print(json.dumps(rows[-8:],indent=2))
