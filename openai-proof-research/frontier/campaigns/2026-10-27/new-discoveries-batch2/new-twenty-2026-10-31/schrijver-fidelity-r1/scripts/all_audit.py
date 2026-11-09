exec(compile((__import__('pathlib').Path(__file__).parent/'spot.py').read_text().split('mods=')[0],str(__file__),'exec'))
r=subprocess.run([sys.executable,'-I',str(l/'scripts/run_capped.py'),str(l/'logs/all-source-declaration-audit.log'),str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true','AuditRound5.lean'],cwd=e/'src',env=env)
raise SystemExit(r.returncode)
