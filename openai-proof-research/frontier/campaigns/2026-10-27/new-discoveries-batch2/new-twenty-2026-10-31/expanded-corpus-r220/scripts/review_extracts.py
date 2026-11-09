import pathlib,re,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1];out={}
for p in (L/'outputs').glob('*-clean.txt'):
 key=p.stem.replace('-clean','');s=p.read_text();lines=s.splitlines();idx=[i for i,l in enumerate(lines) if re.match(r'(Conjecture|Question|Problem) \d',l)]
 extracts=[{'line':i+1,'text':'\n'.join(lines[max(0,i-2):i+7])} for i in idx]
 out[key]={'extracts':extracts,'printed_figures':[l[:500] for l in lines if re.match('Figure [0-9]',l)]}
(L/'outputs/source-review-extracts.json').write_text(json.dumps(out,indent=2))
for k in ['366512','366515','366563','366634','366697','366751','366962','367074','367093','367097','367142','367313']:
 print('\nID',k)
 for x in out.get(k,{}).get('extracts',[]): print(x['text'][:1100])
