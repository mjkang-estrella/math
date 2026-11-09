"""Root documentary verification of r530 (zero qualified survivors, root hand-check of the 352895 argument) and the r532 metadata packet with a structured-family ranking. No other root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r530';assert not (P/'expanded-corpus-r532').exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert m['file_count']==185==len(m['sha256'])
names=set()
for n,h in m['sha256'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==h,n
aex=m['self_exclusions'];assert set(aex)=={'MANIFEST.json','guard.lock','seal_manifest.output.txt','seal_manifest.receipt.json','search-charge.lock'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert names<=inventory and inventory-names<=set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r530.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];bind=read(A/'literal-bindings.json');assert len(ids)==len(bind)==20 and set(ids)==set(map(int,bind))
brief=(A/'ACTUALBRIEF.md').read_text();assert all(str(i) in brief for i in ids)
sources={}
for key,v in bind.items():
 q=Path(v['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==v['chunk_sha256'];raw=lines[int(v['line'])-1]
 # This lane hashed and stored each line without its trailing newline, recording the newline separately.
 assert raw.endswith(b'\n') and v['newline'] is True and dg(raw.rstrip(b'\n'))==v['raw_line_sha256'] and raw.decode().rstrip('\n')==v['raw_line']
 obj=json.loads(raw);tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0];assert obj['mathdb_id']==int(key)
 assert dg(token)==v['raw_statement_token_sha256'] and obj['statement']==v['decoded_statement'] and dg(obj['statement'].encode())==v['decoded_statement_sha256'];sources[key]=obj['source_url']
assert not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,3,3,9,['search-responses/search-1.txt','search-responses/search-2.txt','search-responses/search-3.txt'])
ae=guard(A,sorted(A.glob('plans/get-*.json')),ids,dict(attempt=10,success=7,redirect=3,unavailable=1),7)
un=next(e for e in ae if e['event']=='unavailable');assert 'link.springer.com/article/10.1007/s11139-022-00660' in un['url']
inv=read(A/'history-access-inventory.json');allow=read(A/'historical-results-allowlist.json');assert inv['total']==len(allow)==929 and inv['checked']==927 and inv['skipped']==2 and inv['bad']==[] and inv['hash_mismatch']==[]
for name in allow:
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482])
assert (A/'PROPOSALS.md').is_file() and (A/'NETWORK-STOP.md').is_file()

ass='r530 zero qualified survivors, first Claude Opus 5.5 round. 352895: an author-complete proof that for odd p and coprime positive A,B some n has p not dividing phi(An+B), by Dirichlet with a prime or, when p|A and B=1 mod p, a product of two primes. Root hand-checked the three cases and they hold. Root adopts the author recommendation EXCLUDE AS ROUTINE, credit 0, as a source-ingredient extension: source Proposition 3.5 already picks a prime by Dirichlet, and the two-prime variant closes the single remaining case, the same pattern as prior source-ingredient exclusions. Strongest dissent recorded: it is a deliberate printed conjecture, the authors wrote that their methods cannot address it, and no earlier proof was found in one bounded search. The user may overrule. 372582: routine Weil reduction, expensive Lean, zero. 381174: direct application of Komlos-Pintz-Szemeredi, zero, very expensive Lean. 352894 and 318354 are proved in their own sources, zero. 370850 and 320444 partial. Twelve others parked after the literal only. Disclosed deviations: the get_g8 runner receipt shows exit 0 although the guard exited 1 because of a wrapper sys.exit(0), and one direct ls of the lane plans directory ran outside the runner. This lane hashed corpus lines without their trailing newline; root re-derived all twenty against the corpus in that form. Verified 185 manifest files, 20 corpus bindings, 13 frozen, 10 charged GET hops (7 PDF, 3 redirects, 1 rejected cookie cycle), 3 searches / 3 strings with responses saved. Credit 0, 57/80.'
work='Springer article DOI 10.1007/s11139-022-00660-7, identity unconfirmed'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after an automatic cookie redirect cycle was rejected by the guard; no retry.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=185,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,history_inventory=inv,model='claude-opus-5-5',scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_352895_EXCLUDED_ROUTINE_ROOT_HAND_CHECKED_USER_MAY_OVERRULE',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity, a hand check of the short 352895 argument and scientific disposition; no other mathematics by root.')
den=read(ROOT/'inherited-denials-r563.json');den['utc']=now;den['root_r530_scope']=ass;den['root_springer_cookie_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un['url_key'],'doi.org/10.1007/s11139-022-00660-7'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'10.1007/s11139-022-00660-7'})
den['records'].append(dict(url=un['url'],reason=dict(status='cookie redirect cycle',artifact=work,restriction=fs),evidence=dict(path=str(A/'NETWORK-STOP.md'),sha256=sha(A/'NETWORK-STOP.md'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r530-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r564.json';save(denpath,den)

# Structured-family ranking on the discrete pool.
sel=(ROOT/'reserve-discrete-soft-asymp-20261108-r503.py').read_text()
a="    return (bool(ASYMP.search(d.get('statement') or '') or ASYMP.search(d.get('title') or '')), growth,";assert sel.count(a)==1
b="    shape = bool(re.search(r'(?i)\\b(for|on|in|of) (the )?(transitive|trees?|forests?|tournaments?|cographs?|threshold|split|interval|chordal|cycles?|paths?|caterpillars?|complete (bi|multi)?partite|complete|wheels?|grids?|hypercubes?|cubic|outerplanar|series-parallel|regular|bipartite|circulant|cayley|planar|subcubic|permutation graphs?|line graphs?|claw-free)', d.get('title') or ''))\n    return (-shape, bool(ASYMP.search(d.get('statement') or '') or ASYMP.search(d.get('title') or '')), growth,"
sel='# ROOT 2026-11-09 METADATA-ONLY RANKING for r532: discrete pool, with titles naming a specific structured family ranked first. Not scientific review or clearance.\n'+sel.replace(a,b)
S=ROOT/'reserve-structured-family-20261109-r532.py';assert not S.exists();S.write_text(sel)
base=read(ROOT/'r531-config.json')
hist='The user has barred GPT subagents for now. Every mention of GPT-6.1 Sol, Codex or Sol-only in inherited text, and the file name model-policy-sol-only.json, is historical and does not apply to you. No children or fallback.'
note='\n'+ass+'\nThis round returns to the discrete pool, ranked toward conjectures posed for a specific structured family.\n'
base.update(number=532,model='claude-opus-5-5',reasoning='high',service='default',model_line='THIS LANE RUNS ON CLAUDE OPUS 5.5, high effort. '+hist,protected_peers=['transitive-bunkbed-endpoint-assembly-formal-deepseek-r23','expanded-corpus-r531'],completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{530}),peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r530.json','selection-routing-r531.json','selection-routing-bunkbed-assembly-r23.json'}),denials=str(denpath),metadata_selector=str(S),metadata_selector_sha256=sha(S),steering=base['steering']+note)
save(ROOT/'r532-config.json',base);C=Path(base['metadata_constructor'])
spec=importlib.util.spec_from_file_location('discovery_models',C);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r=module.prepare(base)
for name in read(Path(r['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r530-r532-next-routing.json',dict(utc=now,discovery=r,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r530_manifest=185,frozen=13,corpus=20,r532={k:r[k] for k in ['lane','ids','task_sha256','active_peers','target_new','model']},credit=0,accepted_new=57)))
