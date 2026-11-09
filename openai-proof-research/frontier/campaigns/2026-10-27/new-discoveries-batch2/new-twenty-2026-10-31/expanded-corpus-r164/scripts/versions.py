import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/fetch.py').read_text().split("if __name__")[0],str(D/'scripts/fetch.py'),'exec'))
rows=json.loads((D/'extracted.json').read_text());out={}
for i,r in rows.items():
 a=r['source_url'].split('/')[-1];fetch('https://arxiv.org/abs/'+a,'abs-'+i+'.html');p=D/'sources'/('abs-'+i+'.html')
 if p.exists():
  text=p.read_text();out[i]={'arxiv':a,'version_mentions':sorted(set(re.findall(re.escape(a)+r'v\d+',text))),'history_html':text[text.find('Submission history'):text.find('Submission history')+2500]}
(D/'outputs/versions.json').write_text(json.dumps(out,indent=2))
