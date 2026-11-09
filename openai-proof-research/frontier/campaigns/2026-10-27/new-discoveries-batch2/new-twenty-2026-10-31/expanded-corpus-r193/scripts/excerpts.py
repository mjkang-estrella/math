import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1];vs=json.loads((D/'outputs/versions.json').read_text())
for i,v in vs.items():
 if i in ['322924','324843','324899','326345','361148','365224','326700']:continue
 p=D/f"sources/{i}-v{v['versions'][-1]}-pdf.txt";s=p.read_text();lines=s.splitlines();hits=[j for j,z in enumerate(lines) if re.search(r'Conjecture\s+[\d]|CONJECTURE\s+[\d]',z)]
 print('\n###',i)
 for j in hits[-5:]:print('\n'.join(lines[max(0,j-2):j+15]))
