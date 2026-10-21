"""One bounded, prospective project-root scan; private excerpts, not clearance."""
from pathlib import Path
from fnmatch import fnmatchcase
import os, re, json, hashlib, datetime
ROOT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN = ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r113'
PEERS = ['*analytic*r142*','*structural*r148*','*analytic*r143*','*structural*r149*']
OLD = ([f'*arithmetic*r{n}*' for n in range(107,113)]
       + [f'*analytic*r{n}*' for n in range(135,142)]
       + [f'*structural*r{n}*' for n in range(143,148)]
       + ['*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*'])
COARSE = ['*'+s+'*' for s in ['corpus','source','primary','history-derivative','search','inventory','fixture','control','extract','render','vendor','build','copy','copies','frozen','role','formal','manuscript','release','parent','brief','prompt','task','dispatch','intake','review','contribution','correctness','manifest','catalog','family-titles','fetch','acquire','retrieve','finaliz','seal','reading','provenance','snapshot','history','literature','context','inputs','families','family-map','mechanism-hits','-hits','final-paths','evidence','receipt','identities','verify','prepare-']]
EXACT = {'.git','node_modules','__pycache__','.venv','venv','dist','target','private','sources','fresh-arithmetic-discovery-r113'}
PAT = re.compile(r'torus[- ]packet|sextic|quartic.{0,40}order|Source0?15\b|cubic resolvent|multiplier[- ]order|local homothety|Linnik|Einsiedler|Lindenstrauss', re.I)
def deny(name):
    low=name.lower()
    return low in EXACT or any(fnmatchcase(low,p) for p in PEERS+OLD+COARSE)
def main():
    omissions=[]; hits=[]; visited=0; nonutf=0; agents=[]
    for base,ds,fs in os.walk(ROOT,topdown=True,followlinks=False):
        bp=Path(base)
        keep=[]
        for d in sorted(ds):
            q=bp/d
            if deny(d) or q.is_symlink(): omissions.append(str(q.relative_to(ROOT)))
            else: keep.append(d)
        ds[:]=keep
        for f in sorted(fs):
            q=bp/f; rel=q.relative_to(ROOT)
            if deny(f) or q.is_symlink(): omissions.append(str(rel));continue
            if f=='AGENTS.md': agents.append(str(rel))
            if not any(s in rel.parts for s in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']):continue
            try: b=q.read_bytes(); s=b.decode('utf-8')
            except (UnicodeError,OSError):nonutf+=1;continue
            visited+=1
            lines=[{'line':n,'text':line} for n,line in enumerate(s.splitlines(),1) if PAT.search(line)]
            if lines:hits.append({'path':str(rel),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'hits':lines})
    out={'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root':str(ROOT),'predicate':{'peers':PEERS,'old':OLD,'coarse':COARSE,'exact':sorted(EXACT)},'utf8_bodies_scanned':visited,'nonutf_or_errors':nonutf,'omissions':omissions,'agents':agents,'hits':hits,'limits':'No size cutoff, hidden/ignored/JSON included when eligible. Coarse omissions may hide genuine originals; filenames cannot identify every derivative. Snapshot only; no exhaustive history or perfect isolation certificate.'}
    (OWN/'packet/private/search/history-scan.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k not in ['omissions','predicate','hits']},indent=2))
    print('omissions',len(omissions),'hit files',len(hits))
    for x in hits:
        print(x['path'], 'lines',','.join(str(y['line']) for y in x['hits']))
if __name__=='__main__': main()
