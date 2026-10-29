import pathlib,json,re,subprocess
L=pathlib.Path(__file__).resolve().parent
x=json.loads((L/'sources/cox-archive-search.json').read_text());print('ARCHIVE',[(d['identifier'],d.get('title')) for d in x['response']['docs']])
x=json.loads((L/'sources/omega-delta.json').read_text());print('DELTA',x['total_commits'],len(x.get('commits',[])),len(x['files']));print([(d['filename'],d['status']) for d in x['files']])
t=(L/'sources/uq-experts.html').read_text();m=t.find('Moment properties');print('UQ',t[m-600:m+1200])
print('ARIZONA',(L/'sources/liu-arizona-search.html').read_text())
subprocess.run(['pdftoppm','-f','13','-l','13','-scale-to','1400','-png','-singlefile',str(L/'sources/stover.pdf'),str(L/'sources/stover-p13')],check=True)
