from pathlib import Path
import shutil,json,zipfile,hashlib
r=Path(__file__).resolve().parent;p=r/'packet';s=p/'src'
t=(s/'MaskChainBuild.lean').read_text();helpers=t[t.index('private def pairE'):t.index('elab "mask_input')];chain=t[t.index('elab "mask_chain '):]
ensure='''private def sharedMaskR8 (id p n : String) : CommandElabM Expr := do
  let name := Name.str `Percolation.MaskChain ("maskR8_" ++ id)
  if !(← getEnv).contains name then
    liftCoreM <| addDecl (.defnDecl { name := name, levelParams := [], type := mkConst ``MaskRUP.Mask, value := maskE p n, hints := .abbrev, safety := .safe })
  pure (mkConst name)
'''
chain=chain.replace('elab "mask_chain "','elab "mask_chain8 "').replace('let c := maskE cols[1]! cols[2]!','let c ← sharedMaskR8 idx cols[1]! cols[2]!').replace('let m := maskE vals[1]! vals[2]!','let m ← sharedMaskR8 vals[0]! vals[1]! vals[2]!')
(s/'MaskChainBuildR8.lean').write_text('import MaskChainBuild\nopen Lean Elab Command\nnamespace Percolation.MaskChain\n'+helpers+ensure+chain)
order=(p/'module-order.txt').read_text().splitlines();old=zipfile.ZipFile(r/'r7-source.zip').read('module-order.txt').decode().splitlines()
# Restore every generated suffix source from the lane-owned preparer, then transform commands.
g=json.loads((r/'generation.json').read_text());inputs=[];chains=[]
for lo in [5000,13561,14561,18561]:
 inputs+=g[str(lo)]['input_modules']
chains=sorted([m for m in g if m.startswith('R8Chain')],key=lambda m:g[m]['start'])
for m in chains:
 f=s/f'{m}.lean'
 if not f.exists():shutil.copyfile(r/'undelivered'/f.name,f)
 text=f.read_text().replace('mask_chain ','mask_chain8 ')
 if not text.startswith('import MaskChainBuildR8\n'):text='import MaskChainBuildR8\n'+text
 f.write_text(text)
for m in inputs:
 f=s/f'{m}.lean'
 if not f.exists():shutil.copyfile(r/'undelivered'/f.name,f)
neworder=old+inputs+['MaskChainBuildR8']+chains
(p/'module-order.txt').write_text('\n'.join(neworder)+'\n')
for f in s.glob('*.lean'):
 dst=r/'optimized-extracted/src'/f.name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst);assert hashlib.sha256(f.read_bytes()).digest()==hashlib.sha256(dst.read_bytes()).digest()
(r/'optimized-extracted/module-order.txt').write_text((p/'module-order.txt').read_text())
print('Optimized command and full source prepared',len(neworder),'modules')
# Retain the unshared implementation's full logs before any same-name process is replayed.
for f in (r/'logs').rglob('*'):
 if f.is_file():
  q=r/'unshared-logs'/f.relative_to(r/'logs');q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,q);assert hashlib.sha256(f.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest()
cachemods=old+g['5000']['input_modules']
for m in cachemods:
 assert (r/'fresh-extracted/src'/f'{m}.lean').read_bytes()==(r/'optimized-extracted/src'/f'{m}.lean').read_bytes()
 for rel in [f'build/{m}.olean',f'logs/{m}.ok']:
  a=r/'fresh-extracted'/rel;b=r/'optimized-extracted'/rel;b.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(a,b);assert hashlib.sha256(a.read_bytes()).digest()==hashlib.sha256(b.read_bytes()).digest()
