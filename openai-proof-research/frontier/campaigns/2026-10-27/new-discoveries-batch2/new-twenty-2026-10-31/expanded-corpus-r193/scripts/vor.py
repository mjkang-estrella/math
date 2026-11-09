import pathlib,json,re,subprocess,html
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'outputs/versions.json').read_text())
for i,v in x.items():
 for j,doi in enumerate(v['doi']):subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),i+'-vor-'+str(j),'https://doi.org/'+doi],check=True)
for i in x:
 s=(D/f'sources/{i}-abs.body').read_text();m=re.search(r'<td class="tablecell jref">(.*?)</td>',s,re.S)
 print(i,html.unescape(re.sub('<[^>]+>','',m[1])).strip() if m else 'No journal reference in abs page')
