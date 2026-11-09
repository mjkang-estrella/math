exec(compile((__import__('pathlib').Path(__file__).parent/'spot.py').read_text().split('mods=')[0],str(__file__),'exec'))
commands=[('sanity',[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',str(e/'build/ReviewerSanity.olean'),'ReviewerSanity.lean']),('python',[sys.executable,'-I',str(l/'scripts/independent.py')])]
for name,cmd in commands:
 r=subprocess.run([sys.executable,'-I',str(l/'scripts/run_capped.py'),str(l/'logs'/f'{name}.log')]+cmd,cwd=e/'src' if name=='sanity' else l,env=env)
 print(name,r.returncode,flush=True)
