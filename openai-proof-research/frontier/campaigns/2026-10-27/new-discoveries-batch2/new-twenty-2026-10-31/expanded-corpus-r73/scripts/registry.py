# Live registry path screen. Omega: root tree of current HEAD commit -> D5 and Problems subtrees (recursive).
# OpenAI: HEAD recorded; complete preprints listing reused from fresh-corpus-r10 (HEAD unchanged).
import json,sys,pathlib,re,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent)); from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]; S=D/'sources'
head=json.loads((S/'omega-head.json').read_text()); tree=head['commit']['tree']['sha']
get('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{tree}'); time.sleep(1)
root=json.loads((S/'omega-root.json').read_text()); sub={e['path']:e['sha'] for e in root['tree']}
for k in ['D5','Problems']:
  get(f'omega-{k}.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sub[k]}?recursive=1'); time.sleep(1)
ids=[str(x) for x in json.loads((D/'reservation.json').read_text())['ids']]
kw=['collaps','marginal','hierarch','loglinear','log-linear','eriksson','sullivant','fienberg','rinaldo','three-way','threeway','no-three','transportation',
    'sendov','torsion-length','stable-torsion','korkmaz','collinear','cooper','bernoulli','bacher','kellner','zero-sum','gao','colourful','colorful','simplicial-depth',
    'infinitesimal','double-point','fat-point','geramita','pebbl','cap-set','kostov','deligne','oppenheim','huneke','multiplicity','girth','heegaard','majorization','painleve','sylvester','reflexive']
out={'omega_head':head['sha'],'omega_commit_date':head['commit']['committer']['date'],'root_tree':tree}
for k in ['D5','Problems']:
  t=json.loads((S/f'omega-{k}.json').read_text()); paths=[e['path'] for e in t['tree']]
  out[k]=dict(tree_sha=t['sha'],entries=len(paths),truncated=t['truncated'],id_hits={i:[p for p in paths if i in p] for i in ids},
              keyword_hits={w:[p for p in paths if w in p.lower()][:40] for w in kw})
pre=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/sources/registry-preprints.json')
raw=pre.read_bytes(); import hashlib
pj=json.loads(raw); s=json.dumps(pj).lower()
out['openai']=dict(head=json.loads((S/'openai-head.json').read_text())['sha'],preprints_listing=str(pre),preprints_sha256=hashlib.sha256(raw).hexdigest(),
                   id_hits={i:(i in s) for i in ids},keyword_hits={w:len(re.findall(re.escape(w),s)) for w in kw})
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=1)+'\n')
for k in ['D5','Problems']: print(k,out[k]['tree_sha'],out[k]['entries'],out[k]['truncated'],'idhits',sum(map(len,out[k]['id_hits'].values())),{w:len(v) for w,v in out[k]['keyword_hits'].items() if v})
print('openai',out['openai']['head'],'idhits',sum(out['openai']['id_hits'].values()),{w:v for w,v in out['openai']['keyword_hits'].items() if v})
