import json,re,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
pat=r'375093|375205|375277|375522|375561|375685|375704|375777|375850|376070|376096|376097|376179|376183|376276|376277|376299|376344|376345|376357|2606[._-](04854|10885|13472|24016|25493|31702)|2607[._-](00153|03315|06396|15311|16356|19946|20157|24724|25412|26266|26606)|Ostmann|DemoStrong|LengthArea|Transferal|Bisimplicial|Zeolite|Heged|Rapaport|CircuitDouble|CycleDouble|Ohba|SingularPart|PerfectPower|AcyclicSep|EllisKeller|NormDense'
out={}
for k in ['leanpool','openai','omega']:
 x=json.loads((D/f'http/{k}-tree.json').read_text());hits=[o for o in x['tree'] if re.search(pat,o['path'],re.I)];out[k]={'head':json.loads((D/f'http/{k}-head.json').read_text())['sha'],'truncated':x.get('truncated'),'hits':hits}
 print(k,len(x['tree']),x.get('truncated'));print('\n'.join(o['path'] for o in hits)[:14000])
for p in (D/'http').glob('lp-*'):
 if p.name.endswith('.json'):continue
 hits=[l for l in p.read_text().splitlines() if re.search(pat,l,re.I)];out[p.name]=hits;print(p.name,'\n'.join(hits)[:8000])
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
