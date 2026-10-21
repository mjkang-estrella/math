from pathlib import Path
import os,json,re,fnmatch,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r130')
p=json.loads((R/'notes/prospective-isolation.json').read_text())
wild=p['full_path_casefold_wildcards']+p['admin_full_path_wildcards']
cat=re.compile(r'(?:^|[^a-z0-9])(?:'+'|'.join(re.escape(x) for x in p['coarse_component_prefixes'])+r')',re.I)
def banned(path):
    q=path.as_posix().lower()
    return next((x for x in wild if fnmatch.fnmatchcase(q,x)),None) or ('coarse-category' if cat.search(q) else None)
query=re.compile(r'irrationality|Flint[–— -]?Hills|(?:Source|source)[ _-]?0?17\b|logarithmic (?:curve|period)|separated.weight interpolation|Taylor.degree|transverse.index|(?:pi|π).{0,60}(?:approxim|exponent)|(?:approxim|exponent).{0,60}(?:\bpi\b|π)',re.I)
counts={'directories_pruned':0,'files_pruned':0,'utf8_files':0,'nonutf8':0,'symlinks':0}
pruned=[];matches=[];inventory=[]
for base,ds,fs in os.walk('.',topdown=True,followlinks=False):
    b=Path(base)
    kept=[]
    for name in sorted(ds):
        x=b/name; reason=banned(x)
        if x.is_symlink():counts['symlinks']+=1;continue
        if reason:counts['directories_pruned']+=1;pruned.append({'path':str(x),'reason':reason});continue
        kept.append(name)
    ds[:]=kept
    for name in sorted(fs):
        x=b/name;reason=banned(x)
        if x.is_symlink():counts['symlinks']+=1;continue
        if reason:counts['files_pruned']+=1;continue
        data=x.read_bytes()
        try:s=data.decode('utf-8')
        except UnicodeDecodeError:counts['nonutf8']+=1;continue
        counts['utf8_files']+=1;inventory.append(str(x))
        hit=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if query.search(line)]
        if hit:matches.append({'path':str(x),'size':len(data),'sha256':hashlib.sha256(data).hexdigest(),'matches':hit})
(R/'private/navigation/history-matches.json').write_text(json.dumps(matches,indent=2,ensure_ascii=False)+'\n')
(R/'private/navigation/history-inventory.json').write_text(json.dumps({'counts':counts,'admitted':inventory,'pruned_directories':pruned},indent=2)+'\n')
print(json.dumps(counts));print('MATCH FILES',len(matches))
for x in matches:print(x['path'],x['size'],'lines',','.join(str(h['line']) for h in x['matches']))
