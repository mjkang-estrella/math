import os,subprocess,pathlib
root=pathlib.Path(__file__).parent
pkgs=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,LEAN_PATH=':'.join(str(p/'.lake/build/lib/lean') for p in pkgs.iterdir() if p.is_dir()))
p=subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',str(root/'formal/InvariantMinimum.lean')],env=env,text=True,capture_output=True)
print(p.stdout+p.stderr)
raise SystemExit(p.returncode)
