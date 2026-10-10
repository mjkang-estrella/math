import pathlib,json,hashlib,sys
root=pathlib.Path(__file__).resolve().parents[3]
s=root/'frontier/sources/i145_arithmetic_automorphic_discovery'; m=s/'read-manifest.json'
p=pathlib.Path(sys.argv[1]);p=p if p.is_absolute() else root/p
b=p.read_bytes(); lines=b.decode().splitlines();a=int(sys.argv[2]) if len(sys.argv)>2 else 1;z=min(int(sys.argv[3]),len(lines)) if len(sys.argv)>3 else len(lines)
r={'local':str(p.relative_to(root)),'file_sha256':hashlib.sha256(b).hexdigest(),'start':a,'end':z,'passage_sha256':hashlib.sha256('\n'.join(lines[a-1:z]).encode()).hexdigest(),'ending':lines[z-1],'convention':'splitlines; LF joined without appended LF'}
x=json.loads(m.read_text());x['passages'].append(r);m.write_text(json.dumps(x,indent=2)+'\n')
print('READ',r['local'],a,z,'OF',len(lines));print('\n'.join(f'{i+1}: {v}' for i,v in enumerate(lines) if a<=i+1<=z))
