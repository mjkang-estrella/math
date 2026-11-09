from fetch import get,D
import json,re
heads={k:json.loads((D/'sources'/f'{k}-head.json').read_text())['sha'] for k in ['omega','openai']}
repos={'omega':'the-omega-institute/trureturing','openai':'openai/math'}
for k in heads:
 get((f'{k}-root.json',f'https://api.github.com/repos/{repos[k]}/git/trees/{heads[k]}'))
 root=json.loads((D/'sources'/f'{k}-root.json').read_text())
 for e in root.get('tree',[]):
  if e['path'] in (['D5','Problems'] if k=='omega' else ['preprints']):
   get((f'{k}-{e["path"]}.json',e['url']+'?recursive=1'))
paths={}
for p in (D/'sources').glob('*.json'):
 if p.stem in ['omega-D5','omega-Problems','openai-preprints']:
  a=json.loads(p.read_text());paths[p.name]={'truncated':a.get('truncated'),'matches':[e for e in a.get('tree',[]) if re.search(r'37355[2]|373739|374156|374228|374236|374240|374241|374243|374246|374411|374521|374618|374698|374792|374848|374960|375112|375347|375370|375467|[Cc]yclic.?[Rr]amsey|CycRamsey|OrderedRamsey|monotone.?path|alternating.?path|nested.?match|square.?energy|inertia|LaplacianMatching|normal.?set|Fibonacci.*closed|closed.?rich|zeta.*preorder|preorder.?polytope|half.?freq|balanced.?border|symmetric.?chain|CRIM|Column.?Row|complete.?partition|xray|x-ray|reversal.?set|higher.?Bruhat|Ginzburg|permutation.?invariant.?code|cones?.?of.?colou?rings|tree.?group.*fixed',e['path'],re.I)]}
(D/'outputs/registry-screen.json').write_text(json.dumps({'heads':heads,'path_screen_only':paths},indent=2))
print(json.dumps(paths,indent=2))
