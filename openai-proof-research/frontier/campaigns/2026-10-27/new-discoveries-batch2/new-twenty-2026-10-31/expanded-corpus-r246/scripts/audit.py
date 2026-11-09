import pathlib,subprocess,os,sys
D=pathlib.Path(__file__).resolve().parents[1];b='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'
p=subprocess.run([b+'/lean','-j2','-M3500','-DwarningAsError=true',str(D/'lean/Audit.lean')],env={**os.environ,'LEAN_PATH':str(D/'replay/fresh')})
sys.exit(p.returncode)
