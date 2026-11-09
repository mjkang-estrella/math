import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
prov=json.loads((D/'outputs/provenance.json').read_text())
res_in=json.loads((D/'outputs/dispositions.json').read_text())
def rec(name):
    p=D/'sources'/(name+'.receipt.json')
    return json.loads(p.read_text()) if p.exists() else None
out={}
for i in json.loads((D/'reservation.json').read_text())['ids']:
    k=str(i); r=prov[k]; row=r['row']; d=res_in[k]
    absr=rec(f'{k}.abs.html'); pdfr=rec(f'{k}.pdf')
    absf=D/'sources'/f'{k}.abs.html'
    ver=None
    if absf.exists():
        import re
        vs=re.findall(r'\[v(\d+)\]',absf.read_text(errors='replace')); ver=f"v{max(map(int,vs))}" if vs else None
    out[k]={
     'mathdb_id':i,'title':row['title'],'canonical_url':row['canonical_url'],
     'literal_statement':row['statement'],
     'provenance':{'chunk':r['chunk'],'one_based_line':r['one_based_line'],'chunk_sha256':r['chunk_sha256'],
        'raw_sha256':r['raw_sha256'],'statement_sha256':hashlib.sha256(row['statement'].encode()).hexdigest(),
        'raw_copy':f'raw/{k}.jsonl','newline_preserved':(D/f'raw/{k}.jsonl').read_bytes().endswith(b'\n')},
     'source_url':row['source_url'],
     'source_abs_receipt':absr,'source_pdf_receipt':pdfr,
     'current_arxiv_version_seen':ver,
     **d,
     'history_check':'outputs/history-hits.txt (ledgers, results.json, SUMMARY/markdown across frontier/campaigns; only reservation notes in new-twenty ledger.json for 324966, 347137, 404700)',
     'registry_check':'outputs/registry-path-screen.json: live HEADs 2026-11-03 19:10 UTC Omega ada3bf0c12ee20d00efcf8b040282d36ddb76e90 (changed from 86172888), OpenAI/math 4eaee87548250b2682affda7d05d947c05554bae (unchanged); complete D5 (13784 paths) and Problems (1700) trees fetched, path screen only, not semantic clearance',
     'root_acceptance_required':True,'discovery_credit':0,'self_accepted':False}
assert len(out)==20
(D/'results.json').write_text(json.dumps(out,indent=1,ensure_ascii=False)+'\n')
print(len(out),{k:v['outcome'] for k,v in out.items()})
