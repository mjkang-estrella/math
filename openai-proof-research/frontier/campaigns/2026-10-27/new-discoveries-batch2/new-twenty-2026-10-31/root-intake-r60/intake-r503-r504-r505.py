"""Documentary integrity and routing only; no mathematical investigation."""
import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
resource.setrlimit(resource.RLIMIT_AS, (6*1024**3, 6*1024**3))
from pathlib import Path
import json, hashlib, base64, re, datetime, collections
ROOT=Path(__file__).resolve().parent
P=ROOT.parent
CORPUS=P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
def read(p): return json.loads(p.read_text())
def dg(b): return hashlib.sha256(b).hexdigest()
def sha(p): return dg(p.read_bytes())
def save(p,v):
    assert not p.exists(),str(p)
    p.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P/'ledger.json')['accepted_new']==57
chunks={}
specs={503:(136,851,'seal_manifest',dict(attempt=6,success=4,redirect=1,unavailable=1),3,3),504:(117,853,'manifest19',dict(attempt=9,success=8,redirect=1),3,7),505:(59,855,'manifest_terminal',dict(attempt=1,success=1),1,0)}
records={}
for n,(file_count,history_count,terminal,event_counts,search_count,pdf_count) in specs.items():
    A=P/f'expanded-corpus-r{n}'
    route=read(ROOT/f'selection-routing-r{n}.json')
    assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
    manifest=read(A/'SHA256-MANIFEST.json');entries=manifest['files']
    assert len(entries)==file_count
    for name,item in entries.items():
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        q=A/name;assert not q.is_symlink()
        expected=item if isinstance(item,str) else item['sha256']
        assert sha(q)==expected,name
        if isinstance(item,dict):assert q.stat().st_size==item['bytes'],name
    exclusions=manifest['terminal_noncircular_self_exclusions']
    assert set(exclusions)=={'SHA256-MANIFEST.json',terminal+'.receipt.json',terminal+'.output.txt'}
    inventory=set()
    for q in A.rglob('*'):
        assert not q.is_symlink()
        if q.is_file():inventory.add(str(q.relative_to(A)))
    assert inventory==set(entries)|set(exclusions)
    frozen=read(A/'frozen-inputs.json');assert len(frozen)==13
    assert all(Path(name).parent==A and sha(Path(name))==h for name,h in frozen.items())
    before=read(A/'frozen-before.json');after=read(A/'frozen-after.json')
    assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
    ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json')
    assert len(ids)==20 and set(ids)==set(map(int,gates))
    if n==503:
        initial={str(x['id']):x for x in read(A/'original-provenance.json')}
        provenance={str(x['id']):x for x in read(A/'literal-bindings.json')}
    else:provenance=read(A/('originals.json' if n==504 else 'original-bindings.json'))
    assert set(map(int,provenance))==set(ids)
    sources={}
    for key,row in provenance.items():
        chunk=Path(row['chunk']);assert chunk.is_relative_to(CORPUS)
        if str(chunk) not in chunks:
            b=chunk.read_bytes();chunks[str(chunk)]=(dg(b),b.splitlines(keepends=True))
        h,lines=chunks[str(chunk)];assert h==row['chunk_sha256']
        line_number=row['line'] if n!=505 else row['one_based_line']
        raw=lines[line_number-1];obj=json.loads(raw)
        raw_hash=row['raw_sha256'] if n!=505 else row['raw_line_sha256']
        assert raw.endswith(b'\n') and row['newline'] is True and dg(raw)==raw_hash and obj['mathdb_id']==int(key)
        tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw)
        assert len(tokens)==1;token=tokens[0]
        if n==503:
            init=initial[key]
            assert all(init[z]==row[z] for z in ['chunk','chunk_sha256','line','raw_sha256','newline']) and init['object']==obj
            assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw
            assert token.decode()==row['statement_token'] and dg(token)==row['statement_token_sha256'] and dg(obj['statement'].encode())==row['statement_utf8_sha256']
        elif n==504:
            assert base64.b64decode(row['raw_base64'])==raw and row['row']==obj
            assert (A/row['raw_file']).read_bytes()==raw and row['one_based_line']==line_number and row['newline_hex']=='0a'
            assert token.decode()==row['statement_token'] and dg(token)==row['token_sha256'] and dg(obj['statement'].encode())==row['decoded_statement_sha256'] and row['decoded_statement_utf8']==obj['statement']
        else:
            assert base64.b64decode(row['raw_line_base64'])==raw and row['object']==obj
            for field,t in row['statement_tokens'].items():
                ts=re.findall(rb'"'+field.encode()+rb'"\s*:\s*("(?:[^"\\]|\\.)*")',raw)
                assert len(ts)==1 and ts[0].decode()==t['raw_token'] and dg(ts[0])==t['sha256'] and json.loads(ts[0])==t['decoded']==obj[field] and dg(t['decoded'].encode())==t['decoded_sha256']
        literal=gates[key]['literal']
        assert obj['statement']==json.loads(token)==(literal if isinstance(literal,str) else literal['statement'])
        sources[key]=obj['source_url']
    receipts=[]
    for q in sorted(A.glob('*.receipt.json')):
        v=read(q)
        assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['group_rss_guard_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['killed'] is None,q.name
        receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
    assert read(A/(terminal+'.receipt.json'))['exit']==0
    assert all(x['exit']==0 or (n==503 and x['path']=='get_cov_final.receipt.json' and x['exit']==1) for x in receipts)
    budget=read(A/'search-budget.json')
    assert budget==dict(calls_used=search_count,queries_used=3*search_count,maximum_calls=3,maximum_queries=9,charged_before_call=True)
    charges=[json.loads(x) for x in (A/'search-charges.jsonl').read_text().splitlines()]
    assert len(charges)==search_count
    prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
    for i,c in enumerate(charges,1):
        assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
        nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
        response=(f'search-{["one","two","three"][i-1]}-response.json' if n==503 else (f'search{i:02d}-response.json' if n==504 else 'search1-response.json'))
        assert len((A/response).read_text())>1000
    assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
    planfiles=(list((A/'plans').glob('*.json')) if n==503 else (list(A.glob('plan-get*.json')) if n==504 else list(A.glob('*plan.json'))))
    plans={}
    for q in planfiles:
        v=read(q)
        if 'url' in v:plans[dg(json.dumps(v,sort_keys=True).encode())]=v
    events=[];previous='0'*64
    for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
        e=json.loads(line);assert e['seq']==i and e['previous']==previous;previous=dg(line);events.append(e)
        if e['event']=='success':
            q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
        if e['event']=='attempt':
            assert e['plan_sha256'] in plans and e['url'].startswith('https://') and '/server/api/' not in e['url'] and set(e['routes'])<=set(map(str,ids))
    counts=collections.Counter(e['event'] for e in events);assert counts==event_counts,(n,counts)
    assert sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in events if e['event']=='success')==pdf_count
    history=read(A/'history-access.json');history=history['access'] if isinstance(history,dict) else history
    allow=read(A/'historical-results-allowlist.json');assert len(history)==history_count
    forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
    for x in history:
        rel=Path(x['path']).relative_to(P)
        assert not any(t in part.lower() for part in rel.parts for t in forbidden)
        assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
    records[n]=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),verified_manifest_files=file_count,verified_original_bindings=ids,verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,guard_events=dict(counts),search_budget=budget,verified_saved_history_names=history_count,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions,root_scope='Documentary provenance/integrity/routing only; no root mathematical solving/programs/Lean/checkers.')
summaries={
503:'317413 author full uniform fourth-moment proposal and intended all-index covariance-polynomial bridge, NOT independent PASS; literal normalization/AsN/parameter-regime definitions conflict remains decisive HOLD. Cached original0806.0252 actual source read; original/final ENTIRE work now closed afterDOI302/AIP403. Independent review assigned; no silent normalization choice.377567 source rectangle theorem supplies full public adaptation to printed toric contradiction,zero;374251 periodicity mex routes retain precise gaps;other17originals unread.136files20corpusbindings13frozen851savedhistory names verified;6GEThops4payloads3PDF1HTML,1redirect1HTTP403;3search9. Native multi-image presentation failure and unknown transient/writer peaks preserved.',
504:'328851 author full ordinary planar integral-Laplacian congruence proposal, NOT independent PASS; integral cut/dual-flow generation, signed multigraph isometry, reduced-to-full singular congruence and singleton/bridge/loop/multiedge scope require independent audit and actual classical prior-body/significance comparison.349249 palindrome-shift realization unpaid;366097 nonnegative restriction-natural ownership unpaid.321929 actual public proof exact bridge zero;377961 public counterpart proof body/figures unread HOLD.117files20corpusbindings13frozen853savedhistory names verified;9GEThops8payloads7PDF1HTML1redirect,3search9,no new denial. No final/correction/whole-body or resource universality claim.',
505:'Zero complete candidate.391135 cycles route,391147 diagonal-density route and391112 property-B route retain exact unpaid lemmas;391340 repetitions reading is missing-distinctness correction zero. All20original mathematical bodies unread. ExactErdosProblems642 challenge-bearing HTML manually closed at rawbyte31197; transport200/guard success remains unchanged, network stopped no retry/bypass.59files20corpusbindings13frozen855savedhistory names verified;1GEThop1HTMLpayload,1search3strings. No mathematical primary/current status proof from challenge page. Source/task recovery and unknown native/transient/writer peaks retained.'}
den=read(ROOT/'inherited-denials-r515.json');den['utc']=now
for n in [503,504,505]:
    records[n]['scientific_summary']=summaries[n]
    records[n]['root_disposition']='ZERO_QUALIFIED_SURVIVORS'+('_TARGET_ASSIGNED_INDEPENDENT_REVIEW' if n in [503,504] else '')
    den[f'root_r{n}_scope']=summaries[n]
A=P/'expanded-corpus-r503';failure=next(x for x in [json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()] if x['event']=='unavailable')
assert failure['status']==403
restriction='ENTIRE identified Janson-Luczak Susceptibility in subcritical random graphs,0806.0252,JMP49(2008)125207,DOI10.1063/1.2982848 unavailable for ALL NEW body/METADATA/query/host/version/arxiv/author/cache/mirror/DOI/API/indirect deliveries afterDOI302 toAIP403. No retry, identity correction, alternate delivery or indirect recovery. Explicit predelivery cached original/metadata may be read but not final-equivalence evidence. Distinct subcritical-graph/martingale works are not blanket denied.'
den['blocked_keys']=sorted(set(den['blocked_keys'])|{failure['url_key'],'doi.org/10.1063/1.2982848','arxiv.org/abs/0806.0252','arxiv.org/pdf/0806.0252'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'susceptibility in subcritical random graphs','0806.0252','10.1063/1.2982848'})
den['records'].append(dict(url=failure['url'],reason=dict(status=403,artifact='Janson-Luczak Susceptibility in subcritical random graphs',restriction=restriction),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
A=P/'expanded-corpus-r505';manual=read(A/'manual-unavailable.json');payload=(A/'sources/problem642.html').read_bytes()
assert sha(A/'sources/problem642.html')==manual['body_sha256'] and payload.find(manual['marker'].encode())==manual['byte_offset']==31197
restriction642='ENTIRE EXACT ErdosProblems642 page https://www.erdosproblems.com/642 unavailable for ALL NEW host/query/version/cache/mirror/DOI/API/body/METADATA or indirect deliveries after manual challenge-bearing HTML classification at rawbyte31197 beyond guard12000 prefix. Transport200/guard success remains unchanged; no guard network failure invented, no retry/JS/cookie/browser/account/alternate recovery. Distinct original mathematical works are not blanket denied. No mathematical primary/current-status proof from page.'
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'www.erdosproblems.com/642'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'erdosproblems.com/642','erdosproblems642 exact current page'})
den['records'].append(dict(url=manual['url'],reason=dict(status='Manual challenge-bearing HTML;transport200/guard success unchanged',artifact=manual['identity'],restriction=restriction642),evidence=dict(path=str(A/'manual-unavailable.json'),sha256=sha(A/'manual-unavailable.json'),payload_sha256=sha(A/'sources/problem642.html'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
# Mutations begin only after all documentary checks passed.
for n,v in records.items():save(P/f'expanded-corpus-r{n}-parent-integration.json',v)
save(ROOT/'inherited-denials-r516.json',den)
save(ROOT/'r503-r505-intake-report.json',dict(utc=now,records={str(n):dict(files=v['verified_manifest_files'],frozen=13,bindings=20,guard=v['guard_events'],receipts=len(v['runner_receipts'])) for n,v in records.items()},denials=str(ROOT/'inherited-denials-r516.json'),accepted_new=57,credit=0,root_documentary_deviations=['Initial unnecessary broad rg --files AGENTS inventory listed unrelated saved-source instruction paths; no listed bodies were read. Subsequent access used exact ancestor chain and completed target lanes only.','One combined read was truncated; schema and builder-tail details were recovered in smaller exact reads.','Initial intake script exited1 on a local exclusions variable typo before any integration/preparation write; repaired without child artifact changes.'],no_root_mathematical_work=True))
print(json.dumps(dict(verified={n:dict(files=v['verified_manifest_files'],bindings=20,frozen=13,receipts=len(v['runner_receipts']),events=v['guard_events']) for n,v in records.items()},credit=0,accepted_new=57)))
