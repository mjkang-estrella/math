#!/usr/bin/env python3
"""Rebuild the article from this source directory into a NEW output directory.
Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
"""
import argparse,hashlib,json,os,pathlib,shutil,subprocess
p=argparse.ArgumentParser()
p.add_argument('--output',required=True,type=pathlib.Path)
p.add_argument('--tectonic',default='tectonic')
a=p.parse_args();src=pathlib.Path(__file__).resolve().parent;out=a.output.resolve()
if out.exists():p.error('output must be a new directory, outside source')
if src==out or src in out.parents:p.error('output must be outside source directory')
out.mkdir(parents=True)
env=os.environ.copy();env['SOURCE_DATE_EPOCH']='1792195200';env['TZ']='UTC'
cmd=[a.tectonic,'--only-cached','--untrusted','--keep-logs','--keep-intermediates','--reruns','2','--outdir',str(out),'article.tex']
r=subprocess.run(cmd,cwd=src,env=env,capture_output=True,text=True)
(out/'build.stdout').write_text(r.stdout);(out/'build.stderr').write_text(r.stderr)
if r.returncode:raise SystemExit(r.returncode)
log=(out/'article.log').read_text(errors='replace')
problems=[line for line in log.splitlines() if any(t in line for t in ['Overfull','undefined references','undefined citations','LaTeX Warning:','Package hyperref Warning:'])]
version=subprocess.run([a.tectonic,'--version'],capture_output=True,text=True,check=True).stdout.strip()
receipt={'command':cmd,'engine':version,'source_date_epoch':env['SOURCE_DATE_EPOCH'],'exit_code':r.returncode,'layout_or_reference_warnings':problems,'pdf_sha256':hashlib.sha256((out/'article.pdf').read_bytes()).hexdigest(),'source_files':{str(f.relative_to(src)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(src.rglob('*.tex'))}}
(out/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
if problems:raise SystemExit('build completed with warnings requiring inspection')
