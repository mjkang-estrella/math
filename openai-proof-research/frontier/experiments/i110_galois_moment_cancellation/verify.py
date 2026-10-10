"""Offline, READ-ONLY final replay. Require python -B without optimization.
No downloads, writes, bytecode, repair or resealing. --preseal validates only.
"""
import sys
if not sys.dont_write_bytecode or sys.flags.optimize:raise SystemExit('Require python -B without -O')
import os,json,hashlib,re,subprocess,runpy,contextlib,io
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i110_galois_moment_cancellation')
E=Path('frontier/experiments/i110_galois_moment_cancellation')
R=Path('frontier/iterations/i110-galois-moment-cancellation.md')
OLD=Path('frontier/sources/i108_galois_tuple_divisibility')
SEAL=S/'seal.json';SEALHASH=S/'seal.sha256'
DRIFT=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def require(ok,msg):
    if not ok:raise AssertionError(msg)
def guard(event,args):
    if event=='open':
        mode,flags=args[1:3]
        require(not ((isinstance(mode,str) and any(x in mode for x in 'wax+')) or
            (isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND))), 'Write rejected')
    require(event not in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.chown','os.link','os.symlink','os.truncate',
        'socket.connect','socket.bind','socket.getaddrinfo','os.system','os.exec','os.posix_spawn','os.fork'},'Offline/read-only rejected '+event)
    if event=='subprocess.Popen':
        allowed=[['pdftotext','-layout',str(ROOT/p),'-'] for p in
            [S/'external/bby-author-20260211.pdf',OLD/'external/bby-v1.pdf']]
        require(args[1] in allowed,'Subprocess outside selective stdout-only PDF extraction')
sys.addaudithook(guard)
def blob(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(blob(p))
def inventory():
    files=[str(R)]
    for folder in [S,E]:
        for p in (ROOT/folder).rglob('*'):
            require(not p.is_symlink(),'Owned symlink')
            if p.is_file():files.append(str(p.relative_to(ROOT)))
    return sorted(files)
def replay(p,expected):
    out=io.StringIO()
    with contextlib.redirect_stdout(out):runpy.run_path(str(ROOT/p),run_name='__main__')
    value=json.loads(out.getvalue());require(value==js(expected),'Finite replay mismatch '+str(p));return value
def run(preseal):
    files=inventory()
    if preseal:require(not (ROOT/SEAL).exists() and not (ROOT/SEALHASH).exists(),'Preseal refuses existing seal')
    else:
        seal=js(SEAL);require(sha(blob(SEAL))==blob(SEALHASH).decode().strip(),'Seal hash')
        require(files==seal['owned_inventory'],'Exact owned inventory')
        require(set(seal['files'])==set(files)-{str(SEAL),str(SEALHASH)},'Seal scope')
        require(seal['drift_allowed_live_only']==DRIFT,'Drift scope')
        for p,h in seal['files'].items():require(sha(blob(p))==h,'Sealed file '+p)
        v=js(S/'validation-before-seal.json');require(v['exit_code']==0 and v['result']['status']=='PASS','Validation was not successful')
    refs=js(S/'immutable-references.json')
    for row in refs:
        p=row['path'];require(p not in DRIFT and not re.search(r'i10[79]|iteration10[79]',p),'Forbidden active dependency '+p)
        require(sha(blob(p))==row['sha256'],'Immutable reference '+p)
    prompt=blob(S/'original-i110-brief.txt').decode()
    report=prompt.split('--- ORIGINAL I108 REPORT ---\n',1)[1].split('\n--- FINAL PARENT RESPONSE ---',1)[0].strip()+'\n'
    require(report.encode()==blob(S/'original-i108-report.md')==blob('frontier/iterations/i108-galois-tuple-divisibility.md'),'Original I108 report')
    require(sha(report.encode())=='756db8cd8b2cf97037bc4e5adf343ac8baeb34a18b758a35f170aef286d7596e','Original report expected hash')
    require(blob(S/'original-i108-brief-full.txt')==blob(OLD/'original-i108-prompt.txt'),'Original full I108 brief')
    require(prompt.rsplit('--- FINAL PARENT RESPONSE ---\n',1)[1].encode()==blob(S/'original-i108-final-parent-response.json'),'Finalized parent exact response text')
    parent=js(S/'original-i108-final-parent-response.json')
    require(parent['seal_sha256']==sha(blob(OLD/'seal.json'))=='0081d4ceb8f4c724841036d2a16856d89317846a4761006800f5479e4dbbd625','Original seal')
    require(js(S/'original-i108-parent-replay.json')==js('frontier/experiments/i108-parent-verification.json'),'Original parent replay')
    require(parent==js(S/'original-i108-parent-replay.json'),'Finalized parent consistency')
    for row in parent['parent_reading']['complete_files']:require(sha(blob(row['path']))==row['sha256'],'Parent complete file')
    for row in parent['parent_reading']['passages']:
        b=blob(row['path']);t=b.decode();ls=t.splitlines() if row['line_convention'].startswith('splitlines') else t.split('\n')
        require(sha(b)==row['source_sha256'] and sha('\n'.join(ls[row['start']-1:row['end']]).encode())==row['passage_sha256'],'Parent original passage')
    passages=js(S/'passages.json')['passages']
    for row in passages:
        b=blob(row['local']);t=b.decode('utf-8',errors='replace');ls=t.splitlines()
        require(sha(b)==row['sha256'],'Passage source')
        require(len(ls)==row['splitlines_count'] and len(t.split('\n'))==row['lf_split_count'],'Line convention counts')
        require(sha(('\n'.join(ls[row['first']-1:row['last']])+'\n').encode())==row['passage_sha256'],'Passage bytes')
    for row in js(S/'retrievals.json'):
        b=blob(S/'external'/row['name']);require(len(b)==row['bytes'] and sha(b)==row['sha256'],'Primary raw bytes')
    pdfs=js(S/'provenance.json')['new_pdfs']
    require(pdfs==[str(p.relative_to(ROOT)) for p in sorted((ROOT/S/'external').glob('*.pdf'))],'New PDF scope')
    for p in pdfs:
        proc=subprocess.run(['pdftotext','-layout',str(ROOT/p),'-'],capture_output=True,check=False)
        require(proc.returncode==0 and proc.stdout==blob(p+'.txt'),'New selective PDF extraction')
    q=js(S/'query.json');pat=re.compile(q['expression'],re.I);hits=[]
    for row in js(q['domain']):
        for n,line in enumerate(blob(row['local']).decode('utf-8',errors='replace').splitlines(),1):
            for m in pat.finditer(line):hits.append({'path':row['path'],'line':n,'span':list(m.span()),'match':m.group(),'text':line})
    hits.sort(key=lambda r:(r['path'],r['line'],r['span']))
    require((''.join(json.dumps(r,sort_keys=True,ensure_ascii=False)+'\n' for r in hits)).encode()==blob(S/'search.jsonl'),'Exact lexical occurrence multiset')
    require(js(S/'search-summary.json')=={'occurrences':len(hits),'families':sorted({r['path'].split('/')[1] for r in hits})},'Search summary')
    moments=replay(E/'exact_moments.py',E/'exact-moments.json')
    checks=replay(E/'checks.py',E/'checks.json')
    require(len(moments['cases'])==6 and sum(len(c['moment_numerators']) for c in moments['cases'])==56,'Finite moment scope')
    require(all(c['all_exactly_zero'] for c in moments['cases']),'A nonzero finite moment was found')
    # Run inherited verifier last: its stricter subprocess guard remains installed.
    inherited=runpy.run_path(str(ROOT/'frontier/experiments/i108_galois_tuple_divisibility/verify.py'))['run'](False)
    require(inherited==parent['result'],'Frozen I108 evidence replay result')
    return {'status':'PASS','mode':'preseal' if preseal else 'final','read_only':True,'offline':True,'bytecode_disabled':True,
        'owned_files':len(files),'immutable_references':len(refs),'passages':len(passages),
        'original_blobs':inherited['original_blobs'],'inherited_pdf_texts_hash_checked':776,
        'inherited_searches':inherited['searches'],'new_search':{'occurrences':len(hits),'families':len({r['path'].split('/')[1] for r in hits})},
        'external_pdfs_reextracted_new':len(pdfs),'exact_moment_inputs':len(moments['cases']),'exact_support_moments':56,
        'independent_checks':checks,'boundary':'Evidence integrity and exact finite replay only; no arbitrary-group proof or contribution certification.'}
if __name__=='__main__':
    try:
        require(sys.argv[1:] in [[],['--preseal']],'Only optional --preseal supported')
        print(json.dumps(run(sys.argv[1:]==['--preseal']),indent=2))
    except Exception as exc:
        print(json.dumps({'status':'FAIL','type':type(exc).__name__,'message':str(exc)},indent=2));raise SystemExit(1)
