exec(compile(open(__file__.replace('versions.py','collect.py')).read().split('with concurrent.futures.ThreadPoolExecutor')[0],__file__,'exec'))
jobs=[];meta={}
for i,x in data.items():
 s=(p/'sources'/f'{i}.abs').read_text();hist=s[s.find('Submission history'):];ns=sorted(set(map(int,re.findall(r'\[v(\d+)\]',hist))));aid=x['record']['source_url'].split('/abs/')[-1]
 meta[i]={'versions':ns,'journal_refs':re.findall(r'<td class="tablecell jref">(.*?)</td>',s,re.S),'doi':re.findall(r'https://doi.org/[^"< ]+',s)}
 if 'arxiv' in x['record']['source_url']:
  for n in ns:
   jobs.append((f'{i}-v{n}',{'record':{'source_url':'https://arxiv.org/abs/'+aid+'v'+str(n)}}))
(p/'version-inventory.json').write_text(json.dumps(meta,indent=2))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: rows=list(ex.map(job,jobs))
(p/'version-receipts.json').write_text(json.dumps(sum(rows,[]),indent=2));print('versions fetched',len(jobs)); print(json.dumps(meta,indent=2))
