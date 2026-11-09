import pathlib,re,json,sys
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186')
rows=json.loads((L/'reservation.json').read_text())['rows']; out={}
for r in rows:
 i=str(r['mathdb_id']);p=next((L/'sources').glob('*-'+i+'-abs.body'));s=p.read_text(); a=r['source_url'].rsplit('/',1)[1]
 h=s[s.find('Submission history'):s.find('Submission history')+5000]
 versions=sorted(set(re.findall(r'\[v(\d+)\]',h)),key=int)
 journal=re.search(r'<td class="tablecell jref">(.*?)</td>',s,re.S)
 out[i]={'arxiv':a,'versions':versions,'journal':re.sub('<.*?>','',journal[1]).strip() if journal else None,'abs_body':str(p)}
 print(i,a,'versions',versions,'journal',out[i]['journal'])
(L/'outputs/versions.json').write_text(json.dumps(out,indent=2))
