import pathlib,subprocess,sys,json
O=pathlib.Path(__file__).resolve().parent
p=subprocess.run([sys.executable,str(O/'verify.py'),'--corrupt-statement'],capture_output=True,text=True,timeout=30)
(O/'expected-corruption-failure.stdout').write_text(p.stdout);(O/'expected-corruption-failure.stderr').write_text(p.stderr)
assert p.returncode!=0
(O/'expected-corruption-result.json').write_text(json.dumps({'expected_nonzero':True,'actual_exit_code':p.returncode,'bound_seconds':30,'alteration':'in-memory assigned statement hash; no upstream mutation'},indent=2))
