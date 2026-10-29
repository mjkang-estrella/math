import json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
history=[]
for i in range(4):
 j=json.loads((L/f'history-{i}.json').read_text())
 history.append({k:j[k] for k in ['shard','paths','bodies','hits','seconds','extensions_omitted','oversized','binary_paths','errors']})
reg={n:json.loads((L/f'sources/{n}-head.json').read_text())['sha'] for n in ['omega','openai']}
prov=dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),lane=str(L),status='NO NOMINEE',credit_claimed=0,counts=dict(additional=9,total=39,next=40),source_http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()],guard=dict(path=str(guard),sha256=sha(guard),AS_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,BLAS_threads=1),history_shards=history,history_receipt=json.loads((L/'history-receipt.json').read_text()),registry_heads=reg,registry_delta=json.loads((L/'registry-delta-receipt.json').read_text()),semantic_clearance=False,worldwide_priority_claim=False,ordinary_full_proof=False,external_mutations=False,children=False,git=False,scientific_freeze='scientific-freeze.json',context='context-receipts.json',note='Real retrieval UTC/hash receipts, not inferred publication dates. Source dates and actual read scope in discovery.md. Original r111-r113 science eligible; no whole-lane omission.')
dump('provenance.json',prov)
dump('early-selection-receipt.json',dict(stage='Before first source PDF download at 2026-10-29T23:10:27Z',method='rg over original SUMMARY.md/discovery.md/PROOF.md/*review*.md/*DECISION*.md roles',terms=['jca2591','subadditivity.*convexity','Mulholland','Matkowski.*P.*phi','2504.20539','Randomstrasse','Kikuchi','synchronizing.*regular','regular.*synchronizing'],result='Matkowski hit original r116, read and discarded; subsequent selected source/aliases no original-report hits',limit='Preliminary lightweight filter only; later full hash/alias screen required and completed. Receipt records actual earlier tool sequence, not a contemporaneous saved stdout.'))
dump('failures.json',dict(failures=['Initial combined context terminal output truncated; ledger scopes subsequently read separately','One minified registry metadata terminal output truncated; compact parsed receipt used','2610.09135v2 PDF404; actual current abstract says withdrawn; v1 distinct URL succeeded','One unquoted ampersand query caused shell exit127; quoted query succeeded; no intended body adopted from failure','pdftotext emitted font mismatch warnings'],caps_raised=False,bypass_attempted=False))
print('provenance and bounded omission metadata written')
