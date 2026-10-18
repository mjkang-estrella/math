#!/usr/bin/env python3
"""MIT; copied-public-tree controls. Never mutates the sealed public packet."""
import argparse,json,shutil,subprocess,sys,tempfile
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--expected',required=True);a=p.parse_args();root=Path(__file__).resolve().parent
# Temporary controls live only inside the assigned packet's ignored private area.
(root/'private').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='controls-',dir=root/'private') as td:
    base=Path(td);records=[]
    for kind in ['copy_pass','wrong_anchor','modified','extra','missing','empty_directory','public_symlink','private_symlink']:
        dst=base/kind;shutil.copytree(root,dst,ignore=shutil.ignore_patterns('private'))
        expected=a.expected
        if kind=='wrong_anchor':expected='0'*64
        elif kind=='modified':(dst/'screen-319.md').write_bytes((dst/'screen-319.md').read_bytes()+b'\nmutation\n')
        elif kind=='extra':(dst/'extra.txt').write_text('x')
        elif kind=='missing':(dst/'status.json').unlink()
        elif kind=='empty_directory':(dst/'extra-directory').mkdir()
        elif kind=='public_symlink':(dst/'link').symlink_to('status.json')
        elif kind=='private_symlink':(dst/'private').mkdir();(dst/'private/link').symlink_to('../status.json')
        run=subprocess.run([sys.executable,'-B',str(dst/'verify.py'),'--expected',expected],capture_output=True,text=True)
        success=run.returncode==0;assert success==(kind=='copy_pass'),(kind,run.stdout,run.stderr)
        records.append({'control':kind,'accepted':success,'expected':success==(kind=='copy_pass')})
    print(json.dumps({'status':'PASS','controls':records},indent=2))
