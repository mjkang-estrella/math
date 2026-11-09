import pathlib,json,re,html,sys
D=pathlib.Path(sys.argv[1]);out={}
for p in sorted((D/'sources').glob('abs-*')):
 s=(p/'body').read_text();t=html.unescape(re.sub('<[^>]+>',' ',s));t=re.sub(r'[ \t]+',' ',t);(p/'text.txt').write_text(t)
 i=p.name[4:]; a=t.find('Abstract:');b=t.find('Submission history');end=t.find('Access Paper:')
 out[i]={'abstract':t[a:a+4000].split('Submission history')[0],'history':t[b:b+1500]}
 print(i,out[i]['abstract'][:2300],out[i]['history'][:900])
(D/'outputs/metadata.json').write_text(json.dumps(out,indent=2))
