import os,subprocess,sys
from pathlib import Path
p=Path(__file__).resolve().parents[1];pk=Path(os.environ.get('LEAN_PACKAGES','/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'))
os.environ['LEAN_PATH']=':'.join([str(p/'formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])
lean=os.environ.get('LEAN_BIN','/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
mod=sys.argv[2] if len(sys.argv)>2 else 'Nut'
r=subprocess.run(['python3','-I',str(p/'scripts/run_capped.py'),str(p/'logs'/sys.argv[1]),lean,'-j1','-DwarningAsError=true','-o',str(p/('formal/'+mod+'.olean')),str(p/('formal/'+mod+'.lean'))]);print((p/'logs'/sys.argv[1]).read_text());sys.exit(r.returncode)
