import pathlib,json,subprocess,hashlib
L=pathlib.Path(__file__).resolve().parents[1];r=json.loads((L/'reservation.json').read_text())['rows']
urls=[]
for x in r:
 a=x['source_url'].split('/')[-1]
 if [f'https://arxiv.org/abs/{a}',a+'-abs'] not in urls:urls.append([f'https://arxiv.org/abs/{a}',a+'-abs'])
(L/'scripts/abs-urls.json').write_text(json.dumps(urls))
cmd=['rg','-n','-m','3','-g','SUMMARY.md','-g','CANDIDATE.md','-g','results.json','343214|343333|343389|343399|343435|343470|343552|343574|343608|343739|343948|343950|344055|344313|344319|344331|344369|344577|344636|344693',str(L.parent)]
p=subprocess.run(cmd,capture_output=True,text=True)
(L/'evidence/historical-hits.txt').write_text(p.stdout)
print('Historical hits saved',len(p.stdout))
