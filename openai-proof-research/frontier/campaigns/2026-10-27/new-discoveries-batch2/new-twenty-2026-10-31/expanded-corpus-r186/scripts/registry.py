exec(compile(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186/scripts/fetch.py').read().split("if __name__")[0],'fetch.py','exec'))
head=json.loads(next((L/'sources').glob('*-lean-pool-head.body')).read_text())['sha']
fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+head+'/projects.yml','pool-projects')
d,r=fetch('https://api.github.com/repos/Vilin97/lean-pool/git/trees/'+head+'?recursive=1','pool-tree')
if r.get('status')==200:
 for item in json.loads(d)['tree']:
  if item['path'].startswith('candidates/') and item['type']=='blob': fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+head+'/'+item['path'],'pool-candidate-'+item['path'].replace('/','_'))
for repo,label in [('the-omega-institute/trureturing','omega'),('openai/math','openai')]: fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',label+'-head')
