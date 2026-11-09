import pathlib,subprocess,re,json,html
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('old-*-v*.body'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
for i in ['336863','337667','337675','337704','337871','337877','337900','337903','337952','339273']:
 v=json.loads((D/'outputs/version-inventory.json').read_text())[i]['versions'][-1];s=(D/f'sources/{i}-v{v}.txt').read_text();lines=s.splitlines();matches=[j for j,l in enumerate(lines) if re.search(r'Conjecture(?:\s+|$)',l)];sel=[]
 for j in matches:
  if i=='339273' and not any('univalent' in x for x in lines[j:j+14]):continue
  sel += lines[max(0,j-1):j+10]
 (D/f'outputs/source-excerpt-{i}.txt').write_text('\n'.join(sel));print('\nID',i,'\n','\n'.join(sel)[:2300])
