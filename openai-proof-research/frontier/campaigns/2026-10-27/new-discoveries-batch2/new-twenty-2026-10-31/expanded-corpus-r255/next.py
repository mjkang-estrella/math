import pathlib,json
L=pathlib.Path(__file__).resolve().parent
jobs=[[n+'-root','https://api.github.com/repos/'+repo+'/git/trees/'+json.loads((L/(n+'-head.body')).read_text())['sha']] for n,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing'),('pool','Vilin97/lean-pool')]]
for a in ['1706.09002','1504.05213']:jobs.append([a+'-pdf','https://arxiv.org/pdf/'+a])
for n,u in [('toric-citing','https://ecairncr.github.io/dearborn.pdf'),('prefix-citing','https://www.cis.uoguelph.ca/~sawada/papers/JV_genalgo.pdf')]:jobs.append([n+'-pdf',u])
(L/'next-jobs.json').write_text(json.dumps(jobs))
