exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text().split("if sys.argv[1]=='extract':")[0],__file__,'exec'))
reads=[]
for arg in sys.argv[2:]:
 f,a,b=arg.rsplit(':',2);a=int(a);b=int(b);p=L/'sources'/f;ls=p.read_text().splitlines();print('FILE',f,a,b);print('\n'.join(f'{i+1} {x}' for i,x in enumerate(ls) if a<=i+1<=b));reads.append(dict(file=f,sha256=sha(p.read_bytes()),start=a,end=b,depth='text displayed for review; not automatically entire-paper attestation'))
p=L/'displayed-read-inventory.json';old=json.loads(p.read_text()) if p.exists() else [];js(p.name,old+reads);receipt()
