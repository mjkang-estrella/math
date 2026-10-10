"""Offline read-only verifier: integrity, extraction and finite diagnostics only.
Does not acquire sources, update seals, import bytecode, or write output files.
Exactly four live ledger paths may drift; all other referenced bytes are immutable.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,runpy,subprocess,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i74_relative_symplectic_packing'
E=Path(__file__).resolve().parent
REPORT=ROOT/'frontier/iterations/i74-relative-symplectic-packing.md'
CORPUS=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
EXCLUDED={S/'seal.json',E/'verification.json'}
sha=lambda b:hashlib.sha256(b).hexdigest()
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def require(ok,msg):
    if not ok:raise AssertionError(msg)
def check(p,h):
    b=p.read_bytes();require(sha(b)==h,'Hash drift: '+str(p));return b


def main():
    counts={}
    actual={REPORT}|{p for d in [S,E] for p in d.rglob('*') if p.is_file()}
    actual-=EXCLUDED
    seal=read(S/'seal.json');recorded=[ROOT/x['path'] for x in seal['files']]
    require(len(recorded)==len(set(recorded)),'Duplicate seal records')
    require(set(recorded)==actual,'Sealed-file membership drift')
    for x in seal['files']:
        b=check(ROOT/x['path'],x['sha256']);require(len(b)==x['size'],'Sealed size mismatch')
    counts['sealed_files']=len(recorded)
    refs=read(S/'immutable-references.json')
    require(len({x['path'] for x in refs})==len(refs),'Duplicate immutable references')
    require(not LEDGERS & {x['path'] for x in refs},'Live ledger wrongly immutable')
    for x in refs:
        b=check(ROOT/x['path'],x['sha256']);require(len(b)==x['size'],'Immutable reference size')
    counts['immutable_references']=len(refs)
    ledgers=read(S/'mutable-ledgers.json')
    require({x['path'] for x in ledgers}==LEDGERS and len(ledgers)==4,'Exactly four mutable ledgers required')
    drifts=[]
    for x in ledgers:
        check(ROOT/x['snapshot'],x['sha256'])
        live=sha((ROOT/x['path']).read_bytes())
        if live!=x['sha256']:drifts.append({'path':x['path'],'frozen':x['sha256'],'live':live})
    require(read(ROOT/'sources/upstream.json')['commit']==PIN,'Upstream pin mismatch')
    task=read(S/'task-snapshot.json');require(task['brief']==(S/'full-brief.txt').read_text(),'Brief mismatch')
    tree=read(ROOT/'sources/preprints-tree.json');require(not tree.get('truncated',False),'Truncated tree')
    entries=tree['tree'];blobs={x['path']:x for x in entries if x['type']=='blob'}
    titles=[x for x in entries if x['type']=='tree' and x['path'].count('/')==1]
    paths=subprocess.check_output(['rg','--files','--no-ignore'],cwd=CORPUS,text=True).splitlines()
    inventory=read(ROOT/'frontier/sources/i70_symplectic_geometry_discovery/corpus-inventory.json')
    require(Counter(paths)==Counter(x['path'] for x in inventory),'Corpus file multiset drift')
    for x in inventory:
        b=check(CORPUS/x['path'],x['sha256']);require(blob(b)==x['git_blob']==blobs[x['path']]['sha'],'Corpus blob mismatch')
    screen=read(S/'tree-screen.json')
    require(len(entries)==screen['tree_entries']==13223,'Tree size')
    require(len(titles)==749 and len(blobs)==screen['tree_blobs']==10373,'Full catalogue counts')
    require(len(paths)==screen['corpus_files']==9340,'Corpus size')
    require(sorted(set(blobs)-set(paths))==screen['outside_fixed_corpus'],'Outside-domain listing')
    pattern=r'Symplectic|Seshadri|Packing|Kahler|Kähler|Blowup|Inflation'
    require(screen['title_matches']==[x for x in titles if re.search(pattern,x['path'],re.I)],'Title screen replay')
    counts.update(tree_entries=len(entries),manuscripts=len(titles),corpus_files=len(paths),outside_corpus_blobs=len(screen['outside_fixed_corpus']))
    search={}
    for x in read(S/'searches.json'):
        p=subprocess.run(x['command'],cwd=CORPUS,text=True,capture_output=True)
        require(p.returncode==x['returncode'] and p.stderr==x['stderr'],'Search status drift')
        require(Counter(p.stdout.splitlines())==Counter(x['lines']),'Search line MULTISET drift: '+x['name'])
        search[x['name']]=len(x['lines'])
    counts['search_line_multisets']=search
    extract=runpy.run_path(str(E/'acquire_primary.py'))['extract']
    good=bad=html=pins=0
    prefix='https://raw.githubusercontent.com/openai/math/'+PIN+'/'
    failures=[]
    for p in sorted((S/'primary').glob('*.json')):
        x=read(p)
        if not isinstance(x,dict) or 'url' not in x:continue
        b=check(p.parent/x['body'],x['sha256']);require(len(b)==x['bytes'],'HTTP response length')
        require(bool(x.get('requested_utc')) and bool(x.get('headers')),'Missing HTTP provenance')
        if x['status']==200:good+=1
        else:bad+=1;failures.append({'url':x['url'],'status':x['status'],'failure':x.get('failure')})
        if 'text' in x:
            t=check(p.parent/x['text'],x['text_sha256']);require(extract(b).encode()==t,'HTML extraction replay');html+=1
        if x['url'].startswith(prefix):
            rel=x['url'][len(prefix):];require(blob(b)==blobs[rel]['sha'],'Fresh pinned Git blob mismatch');pins+=1
    pdfs=read(S/'primary/pdf-extractions.json')
    for x in pdfs:
        t=check(S/'primary'/x['text'],x['text_sha256'])
        p=subprocess.run(['pdftotext','-layout',str(S/'primary'/x['body']),'-'],capture_output=True)
        require(p.returncode==0 and p.stdout==t and p.stderr.decode()==x['stderr'],'PDF extraction replay')
    versions=read(S/'current-versions.json')
    for x in versions:
        a=read(ROOT/x['record']);b=check((ROOT/x['record']).parent/a['body'],x['body_sha256'])
        latest=max(map(int,re.findall(re.escape(x['arxiv'])+r'v(\d+)',b.decode())))
        require(latest==x['latest_observed'],'Version observation mismatch')
        v=read(ROOT/x['versioned_record']);require(v['status']==200 and v['url']==f"https://arxiv.org/html/{x['arxiv']}v{latest}",'Version binding')
    counts.update(http_success=good,http_failure=bad,html_replays=html,pdf_replays=len(pdfs),fresh_pin_responses=pins,current_arxiv_versions=len(versions))
    passages=read(S/'passages.json')
    for x in passages:
        b=check(ROOT/x['path'],x['file_sha256']);ls=b.splitlines(keepends=True)
        require(1<=x['first_line']<=x['last_line']<=len(ls),'Invalid passage range')
        require(sha(b''.join(ls[x['first_line']-1:x['last_line']]))==x['passage_sha256'],'Passage bytes mismatch')
    counts['passages']=len(passages)
    history=read(S/'development-failures.json')
    for x in history:
        if 'snapshot' in x:check(S/x['snapshot'],x['sha256'])
    diagnostic=runpy.run_path(str(E/'diagnostics.py'))['main']()
    require(diagnostic==read(S/'diagnostic-results.json'),'Independent finite diagnostic replay')
    counts['finite_diagnostic_groups']=len(diagnostic['groups'])
    old=ROOT/'frontier/experiments/i70_symplectic_geometry_discovery/verify.py'
    replay=subprocess.run([sys.executable,'-B',str(old)],cwd=ROOT,text=True,capture_output=True)
    require(replay.returncode==0,'I70 read-only replay failed: '+replay.stdout+replay.stderr)
    oldresult=json.loads(replay.stdout);frozen=read(S/'i70-replay.json')
    require(frozen['returncode']==0 and oldresult['status']==frozen['result']['status']=='PASS_EVIDENCE','I70 evidence status')
    require(oldresult['counters']==frozen['result']['counters'],'I70 evidence counters drift')
    # Live ledger drift is deliberately not compared between the two replay times.
    counts['i70_replay']='PASS_EVIDENCE (not an analytic axiom)'
    links=[]
    for target in re.findall(r'\]\(([^)]+)\)',REPORT.read_text()):
        if target.startswith(('http:','https:','#')):continue
        require((REPORT.parent/target.split('#')[0]).resolve().exists(),'Broken report link: '+target);links.append(target)
    counts['local_report_links']=len(links)
    return {'status':'PASS_EVIDENCE','scope':'Retained bytes, reproducible extraction and exact finite algebra only; RP remains unproved/unrefuted.','counts':counts,'mutable_ledger_drift':drifts,'retained_http_failures':failures,'analytic_status':'I74 author audit of I70 scopes passes; new restricted author deductions are not independently accepted.','contribution':'Technical only; no nomination or count increment.'}

if __name__=='__main__':
    try:result=main()
    except Exception as e:
        print(json.dumps({'status':'FAIL_EVIDENCE','error':str(e)},indent=2));sys.exit(1)
    print(json.dumps(result,indent=2,sort_keys=True))
