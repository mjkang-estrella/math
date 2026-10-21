#!/usr/bin/env python3
"""Bounded authored-path search. Prune components before descent or body selection."""
from pathlib import Path
import os,re,json,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[3]
OUT=ROOT/'private/search'
OUT.mkdir(parents=True,exist_ok=True)
ACTIVE=re.compile(r'analytic.*r13[5-8]|arithmetic.*r10[7-9]|structural.*r14[34]|t185r144-|t177c143-|t373e135-|k369r134-|t088p133-',re.I)
DERIV=re.compile(r'(^|[-_.])(inputs?|copies|copied|copy|corpus|inventor[^/]*|fixtures?|controls?|sources?[0-9]*|preprints|upstream[^/]*|context|recovery-context|search[^/]*|\.venv|venv|site-packages|intro|primary|primaries|literature|history|frozen|render[^/]*|vendor|release|formal[^/]*|manuscript[^/]*|roles?|active|reviews?|reviewer|proof-r[0-9]+|contribution-r[0-9]+|parent|intakes?|briefs?|dispatch[^/]*|task[^/]*|capabilit[^/]*|replay[^/]*|catalog[^/]*|manifest|family[^/]*|CONTENTS|fetch[^/]*|snapshots?|receipts?|checkpoints?-copy|archive[^/]*|cache|node_modules|\.git)([-_.]|$)',re.I)
PATTERN=r'general[isz]ed?.{0,12}truncat|wild.{0,20}truncat|uniform.{0,20}matroid|Gollin|Geschke|local.interpolat|conditional.{0,12}rank|fundamental.{0,40}(circuit|support)|rank.{0,16}probe|liminf.{0,50}(rank|matroid)|source.?185|packing.covering'
selected=[];pruned=[];skipped=[]
roots=['campaigns','iterations','experiments','proposals','scouts','notes','findings']
for name in roots:
    start=PROJECT/'frontier'/name
    if not start.exists():
        skipped.append({'path':str(start.relative_to(PROJECT)),'reason':'root absent'});continue
    for base,ds,fs in os.walk(start,topdown=True,followlinks=False):
        for n in list(ds):
            p=Path(base)/n
            why='active' if ACTIVE.search(n) else 'derivative/role' if DERIV.search(n) else 'symlink' if p.is_symlink() else None
            if why: ds.remove(n);pruned.append({'path':str(p.relative_to(PROJECT)),'reason':why})
        for n in fs:
            p=Path(base)/n
            if ACTIVE.search(n) or DERIV.search(n) or p.is_symlink():
                skipped.append({'path':str(p.relative_to(PROJECT)),'reason':'component/flat derivative or symlink'});continue
            selected.append(str(p.relative_to(PROJECT)))
(OUT/'selected-paths.json').write_text(json.dumps(selected,indent=2)+'\n')
(OUT/'pruning.json').write_text(json.dumps({'directories':pruned,'files_or_roots':skipped},indent=2)+'\n')
matches=[];failures=[];begin=time.monotonic()
for i in range(0,len(selected),160):
    if time.monotonic()-begin>180:
        failures.append({'unsearched_from_index':i,'reason':'180 second total bound'});break
    batch=selected[i:i+160]
    try:
        r=subprocess.run(['rg','--hidden','--no-ignore','-i','-l','-e',PATTERN,'--',*batch],cwd=PROJECT,capture_output=True,timeout=30)
        matches+=r.stdout.decode('utf8','replace').splitlines()
        if r.returncode not in [0,1]: failures.append({'batch_index':i,'code':r.returncode,'stderr':r.stderr.decode('utf8','replace')})
    except subprocess.TimeoutExpired: failures.append({'batch_index':i,'reason':'30 second batch timeout'})
(OUT/'matching-paths.json').write_text(json.dumps(matches,indent=2)+'\n')
(OUT/'summary.json').write_text(json.dumps({'selected':len(selected),'pruned_directories':len(pruned),'skipped_files_or_roots':len(skipped),'matched':len(matches),'failures':failures,'pattern':PATTERN,'limits':'hidden/ignored included, no filesize cutoff; rg binary exclusion; coarse prepruning can omit genuine originals; path matches are navigation, not semantic reads; not history clearance'},indent=2)+'\n')
print(json.dumps({'selected':len(selected),'matched':len(matches),'failures':failures}))
