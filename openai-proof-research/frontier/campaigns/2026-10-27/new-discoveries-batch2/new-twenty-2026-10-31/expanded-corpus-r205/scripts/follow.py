import pathlib,sys,json,re,runpy,html
D=pathlib.Path(sys.argv[1]).resolve();sys.argv=sys.argv[:2];f=runpy.run_path(str(D/'scripts/fetch.py'));fetch=f['fetch']
fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/projects.yaml','pool-projects.yaml')
for p in sorted((D/'sources').glob('abs-*/body')):
 t=p.read_text();i=p.parent.name[4:];o=json.loads((D/'extracted.json').read_text())[i]
 if 'arxiv' not in o['source_url']:continue
 vers=sorted(set(re.findall(r'\[v(\d+)\]',t)),key=int)
 for v in vers[:-1]:fetch(o['source_url'].replace('/abs/','/pdf/')+'v'+v,'version-'+i+'-v'+v)
 m=re.search(r'href="(https://doi.org/[^"<>]+)',t)
 if m:fetch(html.unescape(m[1]),'vor-'+i)
for label,url in [('mbv-proof','https://eprints.lse.ac.uk/114634/1/On_complete_classes_of_valuated_matroids.pdf'),('match-vor','https://numdam.org/item/10.5802/alco.169.pdf'),('group-vor','https://research-repository.st-andrews.ac.uk/bitstream/10023/25156/1/Kelsey_2022_Maximal_cocliques_in_CombinatorialTheory_2_1_56879_CCBY.pdf'),('dilates-new','https://arxiv.org/abs/2503.10665')]:fetch(url,label)
