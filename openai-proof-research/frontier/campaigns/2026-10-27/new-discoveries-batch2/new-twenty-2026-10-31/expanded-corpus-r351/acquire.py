exec(compile((__import__('pathlib').Path(__file__).parent/'worker.py').read_text().split('code=0')[0], 'worker.py','exec'))
r=json.loads(read(P/'reservation.json')); pairs=[]
for row in r['rows']:
 a=row['source_url'].rsplit('/',1)[1]; pairs.append([a+'.html','https://arxiv.org/html/'+a])
pairs += [['leanpool.html','https://leanpool.com/'],['leanprover.html','https://leanprover-community.github.io/leanprover-community/'],['projects.yml','https://raw.githubusercontent.com/leanprover-community/mathlib4/master/docs/overview.yaml']]
save('fetch-primary.json',pairs)
