import pathlib,re,json
L=pathlib.Path(__file__).resolve().parents[1];out={}
for p in sorted((L/'sources').glob('*-abs/body')):
 a=p.parent.name[:-4];s=p.read_text();versions=sorted(set(map(int,re.findall(r'/abs/'+re.escape(a)+r'v(\d+)',s))))
 items=[]
 for v in versions:
  pp=L/'sources'/(f'{a}-pdf' if v==max(versions) else f'{a}-v{v}-pdf')/'text.txt'
  lines=pp.read_text().splitlines();items.append({'version':v,'text':str(pp.relative_to(L)),'conjecture_lines':[{'line':i+1,'text':'\n'.join(lines[max(0,i-1):i+10])} for i,z in enumerate(lines) if re.match('^Conjecture',z)]})
 out[a]=items
(L/'evidence/all-version-conjecture-comparison.json').write_text(json.dumps(out,indent=2))
print('Compared version excerpt inventories for',len(out),'sources')
