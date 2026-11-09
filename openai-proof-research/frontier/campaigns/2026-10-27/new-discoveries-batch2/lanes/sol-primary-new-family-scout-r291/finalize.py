from run import *
import xml.etree.ElementTree as E
# Complete administrative reads and reconciliation; do not mutate shared files.
ledger=json.loads((L/'administrative/ledger.json').read_text())
prior=json.loads((L/'administrative/prior-campaign-context.json').read_text())
dump('context-reconciliation.json',{'accepted_count':ledger['accepted_count'],'total':ledger['total_accepted_count'],'next':ledger['next_global_outcome_number'],'current_accepted_titles':[x.get('title') for x in ledger['accepted']],'first_campaign_accepted_titles':[x.get('title') for x in prior['accepted']]})
bindings=[]
for line in (L/'access.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'sha256' not in r:continue
 matches=[p for p in (L/'primary').iterdir() if p.is_file() and sha(p)==r['sha256']]
 assert len(matches)==1
 r['local']=str(matches[0]);r['final_hash_match']=True;bindings.append(r)
for line in (L/'derived.jsonl').read_text().splitlines():
 r=json.loads(line);assert sha(pathlib.Path(r['source']))==r['sha256'];assert sha(pathlib.Path(r['text']))==r['text_sha256']
dump('source-bindings.json',bindings)
chrono=[]
for p in (L/'primary').glob('*.xml'):
 a=sha(p);root=E.fromstring(p.read_bytes());assert a==sha(p)
 for e in root.findall('{*}entry'):
  chrono.append({'feed':str(p),'id':e.find('{*}id').text,'title':e.find('{*}title').text,'published':e.find('{*}published').text,'updated':e.find('{*}updated').text})
dump('chronology.json',chrono)
dump('provenance.json',{'date':'2026-10-30','lane':str(L),'worker':'solo research sub-agent; no children','source_policy':'versioned public arXiv PDFs frozen at retrieval; text extraction bound to binary before reading; local final hashes checked','administrative_policy':'snapshots only, no shared mutation','historical_references':'compact path/hash references in history-index and semantic-dedup; no recursive copies','guard':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','caps':{'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'env':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'novelty_status':'not cleared','scientific_status':'unresolved, zero discoveries','process_deviations':'failures.md','current_registry_head':'UNKNOWN; denied routes not retried','google_requests':0})
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
dump('MANIFEST.json',manifest)
print('finalized',len(manifest),'files;',len(bindings),'retrievals;',ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])
