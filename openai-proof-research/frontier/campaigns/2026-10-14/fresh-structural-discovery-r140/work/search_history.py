from pathlib import Path
import subprocess,json,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r140')
exclude=['**/.git/**','**/fresh-arithmetic-discovery-r103/**','**/*arithmetic*r104*/**','**/*analytic*r134*/**','**/*[tT]009[pP]102*/**','**/*[tT]088[pP]133*/**','**/discovery-analytic-r133-parent/**','**/fresh-structural-discovery-r140/**','**/preprints-tree.json','**/tree.json','**/CONTENTS.md','**/sources/preprints/**','**/upstream/preprints/**','**/node_modules/**','**/.lake/**']
pat=r'Saxl|universal.tensor.square|tensor.product.Markov|Kronecker.*(walk|mixing|staircase)|staircase.*(character|Kronecker|tensor)|tensor.*Plancherel'
args=['rg','--hidden','--no-ignore','-l','-i',pat,'frontier']
for e in exclude:args+=['-g','!'+e]
a=subprocess.run(args,capture_output=True);(R/'packet/private/search/history205-paths.txt').write_bytes(a.stdout);(R/'packet/private/search/history205-stderr.txt').write_bytes(a.stderr)
files=a.stdout.decode().splitlines();(R/'packet/private/search/history205-query.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),argv=args,returncode=a.returncode,files=len(files),limit='no file-size or match-count cutoff; text search, binary ignored; paths are navigation only'),indent=2)+'\n')
print('matching files',len(files)); print('\n'.join(f for f in files if not any(x in f for x in ['/inputs/','/snapshots/','/frozen/','/sources/','/private/','/work/']) )[:14000])
