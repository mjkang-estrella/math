from pathlib import Path
import json,re
L=Path(__file__).resolve().parent;D=L/'http';out={};j=[]
for i,x in json.loads((L/'records.json').read_text()).items():
 p=D/(i+'-abs.html');b=p.read_text();a=x['record']['source_url'].split('/abs/')[-1];v=sorted(set(re.findall(re.escape(a)+r'v(\d+)',b)),key=int)
 out[i]={'arxiv_id':a,'versions':v,'journal_ref':re.findall(r'<td class="tablecell jref">(.*?)</td>',b,re.S),'scope':'abs version-history scan; no all-version-body clearance'}
 if i in ['329705','361905','329726','329995','334903','358939']:
  for z in v:j.append([i+'v'+z+'.pdf','https://arxiv.org/pdf/'+a+'v'+z])
(L/'version-inventory.json').write_text(json.dumps(out,indent=2));(L/'versions-plan.json').write_text(json.dumps(j));print(json.dumps(out,indent=2)[:5000])
