# Root r503 version: documentary metadata selector with asymptotic language as a soft penalty. Earlier constructor/selector remain unchanged.
"""Root-only documentary packet construction; no mathematics, network or delegation."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,sys,runpy,contextlib,io,shutil
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,d):
 assert not q.exists(),str(q)
 q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2)+'\n')
def prepare(config):
 number=config['number'];assert isinstance(number,int)
 L=P/f'expanded-corpus-r{number}';assert not L.exists()
 ledger=json.loads((P/'ledger.json').read_text());current=ledger['accepted_new'];assert ledger['target_new']==60 and ledger['previous_accepted']==39
 active=config['protected_peers'];assert isinstance(active,list) and len(active)<=2 and all('/' not in x for x in active)
 quarantined=set(config.get('quarantined_discovery_numbers',[395,463,466]))|{395,463,466}
 completed=[n for n in config['completed_discovery_numbers'] if n not in quarantined];assert all(isinstance(n,int) and f'expanded-corpus-r{n}' not in active for n in completed)
 denpath=Path(config['denials']);assert denpath.parent==ROOT and denpath.is_file()
 peer_ids=set(config.get('excluded_ids',[]));peer_sources=set(config.get('excluded_sources',[]))
 for meta_name in config.get('peer_routing_files',[]):
  q=ROOT/meta_name;assert q.parent==ROOT
  meta=json.loads(q.read_text());peer_ids.update(meta['ids']);peer_sources.update(meta['sources'])
 def normalize(s):
  s=(s or '').strip().replace('http://','https://').rstrip('/').replace('arxiv.org/pdf/','arxiv.org/abs/')
  return re.sub(r'v\d+$','',re.sub(r'\.pdf$','',s))
 peer_sources={normalize(s) for s in peer_sources}
 source=(ROOT/'integrate-cover-r2-prepare-r434.py').read_text();tail=source[source.index('# Metadata selector:'):];tail=tail[:tail.rfind('\nprint(')]
 old_active="active=['cmdrr-five-three-formal-sol-r3','shoe-pair-discrepancy-formal-sol-r2']"
 old_peers="peer_ids={326555,324571};peer_sources={'https://arxiv.org/abs/1310.5240','https://arxiv.org/abs/1211.6486'}"
 assert old_active in tail and old_peers in tail
 tail=tail.replace(old_active,'active='+repr(active)).replace(old_peers,'peer_ids='+repr(peer_ids)+';peer_sources='+repr(peer_sources))
 # Protected flat parent-integration names need the same pre-access filter as directories.
 old_history_filter=" if len(rel.parts)>1 and (rel.parts[0] in active or rel.parts[0]=='expanded-corpus-r395' or any(w in rel.parts[0].lower() for w in protected_words)):continue"
 new_history_filter=" if any(part in active or part in "+repr({f'expanded-corpus-r{n}' for n in quarantined}|{f'expanded-corpus-r{n}-parent-integration.json' for n in quarantined})+" or any(w in part.lower() for w in protected_words) for part in rel.parts):continue"
 old_parent_filter=" if q.name.endswith('.json') and 'parent-integration' in q.name and q.is_file():filtered[str(q)]=sha(q)"
 new_parent_filter=" if q.name.endswith('.json') and 'parent-integration' in q.name and q.name not in "+repr({f'expanded-corpus-r{n}-parent-integration.json' for n in quarantined})+" and not any(w in q.name.lower() for w in protected_words) and q.is_file():filtered[str(q)]=sha(q)"
 assert old_history_filter in tail and old_parent_filter in tail
 tail=tail.replace(old_history_filter,new_history_filter).replace(old_parent_filter,new_parent_filter)
 candidate_pool=config.get('candidate_pool',400);assert isinstance(candidate_pool,int) and 120<=candidate_pool<=1000
 assert "os.environ['RESERVE7_N']='120'" in tail
 tail=tail.replace("os.environ['RESERVE7_N']='120'",f"os.environ['RESERVE7_N']='{candidate_pool}'")
 year_floor=config.get('year_floor',2012);assert isinstance(year_floor,int) and 1900<=year_floor<=2026
 assert "os.environ['YEAR_FLOOR']='2012'" in tail
 tail=tail.replace("os.environ['YEAR_FLOOR']='2012'",f"os.environ['YEAR_FLOOR']='{year_floor}'")
 tail=tail.replace('selection-routing-r434.json',f'selection-routing-r{number}.json').replace('for num in range(421,434):','for num in '+repr(completed)+':')
 tail=tail.replace("'accepted_new':55",f"'accepted_new':{current}").replace('55/60',f'{current}/60').replace("'frozen_bindings':12","'frozen_bindings':13")
 tail=tail.replace('Root separated this20 from retained active IDs326555/324571 and primary URLs1310.5240/1211.6486 using immutable metadata.','Root excluded retained sibling IDs/sourceURLs and configured held targets using ROOT routing metadata; no active-child file access. Metadata selection is not scientific clearance.')
 tail=tail.replace("shutil.copyfile(denpath,L/'inherited-denials.json')","shutil.copyfile(ROOT/'charge_search.py',L/'charge_search.py')\nshutil.copyfile(denpath,L/'inherited-denials.json')")
 tail=tail.replace("'historical-results-allowlist.json','TASK.txt']","'historical-results-allowlist.json','TASK.txt','charge_search.py']")
 extra_reviews=['binary-projection-ratio-source-review-sol-r1','graph-wavelet-minimax-source-review-sol-r1','graph-wavelet-minimax-primary-comparison-sol-r2','tree-hom-hitting-source-review-sol-r1','random-zero-pattern-source-review-sol-r1']
 extra_reviews=[x for x in extra_reviews if x not in active]
 tail=tail.replace("'cover-ratio-primary-comparison-sol-r2']:","'cover-ratio-primary-comparison-sol-r2',"+','.join(repr(x) for x in extra_reviews)+']:' )
 tail=tail.replace('task=core+latest',"core=core.replace('Current55/60 beyond39 prior,94total.',"+repr(f'Current{current}/60 beyond39 prior,{current+39}total.')+").replace('Current accepted55 includes',"+repr(f'Current accepted{current} includes')+").replace('Twelve immutable frozen bindings','Thirteen immutable frozen bindings')\ntask=core+latest")
 latest='\nLATEST ROOT ROUTING authoritative, supersedes historical handbacks: '+f'{current}/60 beyond39 prior,{current+39}total. ONLYGPT-6.1Solhigh/default ALLagents,nochildren/fallback. Root orchestrates/documentary metadata only. ACTIVE/PLANNED '+', '.join(active)+' entirely protected evenmetadata/reservation/stat/read/hash/glob/list/poll.\n'+config['steering']+'\nHISTORY ACCESS FIX: apply protected-name filtering to EVERY relative path component, including a flat campaign-root basename, BEFORE stat/open/hash. In particular hat-bipartite-cycle-formal-parent-integration-r1.json and r2.json are protected despite their root location or any old allowlist entry. All formal/code-loop/Polynexus/crown/bunkbed/tournament/Hat campaign bodies and integration files are protected. Completed allowlisting does not override the file boundary. r463 and r466 are quarantined after this breach; do not read/reuse their research outputs, source acquisitions, or mathematical claims as evidence or candidates. Their reservations remain occupied for disjoint routing. The supplied history allowlist has been filtered upstream as an additional safeguard.\n'
 tail=re.sub(r"latest='''.*?'''",lambda _:'latest='+repr(latest),tail,count=1,flags=re.S)
 selector=ROOT/'reserve-discrete-soft-asymp-20261108-r503.py';assert sha(selector)=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
 now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 tail=tail.replace('reserve-finite-flagship-later-20261107-r390.py','reserve-discrete-soft-asymp-20261108-r503.py')
 namespace=dict(globals());namespace.update(dict(L=L,ledger=ledger,now=now,denpath=denpath))
 exec(compile(tail,str(ROOT/'integrate-cover-r2-prepare-r434.py')+f'#complete-metadata-r{number}','exec'),namespace)
 reservation=json.loads((L/'reservation.json').read_text());assert len(reservation['ids'])==20 and not set(reservation['ids'])&peer_ids
 assert not {normalize(x.get('source_url')) for x in reservation['rows']}&peer_sources
 frozen=json.loads((L/'frozen-inputs.json').read_text());assert len(frozen)==13 and all(sha(Path(n))==h for n,h in frozen.items())
 assert not (L/'bootstrap-receipt.json').exists()
 ready=dict(utc=now,lane=str(L),ids=reservation['ids'],task_sha256=sha(L/'TASK.txt'),frozen=13,accepted_new=current,target_new=60,model='gpt-6.1-sol',reasoning='high',service='default',latest_denials=str(denpath),active_peers=active,credit=0)
 save(ROOT/f'r{number}-ready.json',ready)
 return ready
if __name__=='__main__':
 assert len(sys.argv)==2
 q=Path(sys.argv[1]).resolve();assert q.parent==ROOT
 print(json.dumps(prepare(json.loads(q.read_text()))))
