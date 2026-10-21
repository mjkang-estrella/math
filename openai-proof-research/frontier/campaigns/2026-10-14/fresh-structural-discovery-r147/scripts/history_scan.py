"""Bounded one-pass authored UTF8 search; no size cutoff; no symlink descent."""
import os, re, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[3]
rounds={"arithmetic":[112,113,111,110,109,108,107],"analytic":[141,142,140,139,138,137,136,135],"structural":[146,145,144,143,147]}
derivatives=re.compile(r'corpus|source|primary|history|search|inventory|fixture|control|extract|render|vendor|build|cop(?:y|ies|ied)|frozen|role|formal|manuscript|release|parent|context|catalog|packet|evidence|ledger|tasks|brief|intake|prompt|dispatch|environment|snapshot|\.git|node_modules|venv|scratch|cache|input|work|payload|private|prior|archive|record|manifest|receipt|screen|shortlist|family|path|task|authentication|verify|replay|validation|audit|seal|check',re.I)
prefixes=('h138-','t185r144-','t177c143-','t373e135-','k369r134-','t088p133-')
def excluded(name):
    low=name.lower()
    return bool(derivatives.search(low) or any(p in low for p in prefixes) or any(re.search(k+r'.*r'+str(n),low) for k,ns in rounds.items() for n in ns))
pattern=re.compile(r'Markov.{0,30}delet|delet.{0,30}Markov|renewal.{0,30}thinn|correlated.{0,20}delet|burst.{0,20}delet',re.I)
counts=dict(utf8=0,nonutf8=0,symlinks=0,pruned_dirs=0,pruned_files=0)
hits=[]
for base in ['frontier','research','experiments','proposals','scouts','notes','findings']:
    start=PROJECT/base
    if not start.is_dir(): continue
    for path,dirs,files in os.walk(start,followlinks=False):
        keep=[]
        for name in dirs:
            p=Path(path)/name
            if excluded(name): counts['pruned_dirs']+=1
            elif p.is_symlink(): counts['symlinks']+=1
            else: keep.append(name)
        dirs[:]=keep
        for name in files:
            if excluded(name): counts['pruned_files']+=1; continue
            p=Path(path)/name
            if p.is_symlink(): counts['symlinks']+=1; continue
            if not p.is_file(): continue
            try: s=p.read_bytes().decode('utf8')
            except UnicodeDecodeError: counts['nonutf8']+=1; continue
            counts['utf8']+=1
            found=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if pattern.search(line)]
            if found: hits.append({'path':str(p.relative_to(PROJECT)),'matches':found})
out={'policy':'component and flat-name prune before descent/read; hidden/ignored/JSON and large UTF8 included; coarse omissions intentional','counts':counts,'hits':hits}
(ROOT/'private/search/focused-history.json').write_text(json.dumps(out,indent=2))
print(json.dumps(counts)); print('hit_files',len(hits))
for h in hits: print(h['path'],[m['line'] for m in h['matches']])
