exec(compile((__import__('pathlib').Path(__file__).parent/'spot.py').read_text().split('mods=')[0],str(__file__),'exec'))
for m in ['EndpointRound5','ClosureAuditRound5']:
 r=subprocess.run([sys.executable,'-I',str(l/'scripts/run_capped.py'),str(l/'logs'/f'checker-fixed-{m}.log'),str(bin/'leanchecker'),m],cwd=e/'src',env=env)
 print(m,r.returncode,flush=True)
