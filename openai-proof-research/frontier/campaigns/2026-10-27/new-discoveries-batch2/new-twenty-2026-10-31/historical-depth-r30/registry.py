import pathlib,json,hashlib,re
W=pathlib.Path(__file__).resolve().parent;P=W.parent/'fresh-corpus-r10/sources';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((W/'sources/registry.json').read_text());assert d['sha']=='4eaee87548250b2682affda7d05d947c05554bae'
r=json.loads((P/'registry-preprints-receipt.json').read_text());p=P/'registry-preprints.json';assert H(p)==r['sha256'];t=json.loads(p.read_text());assert not t['truncated'];assert t['sha']=='3f56f68a176b4494c346091ea0a319651bc217ec'
pat=re.compile('spanning|four.genus|4.genus|porous|hypersurface|concordance|degenerate|Boltzmann|trisection|multilinear|approximate.GCD|sign.pattern|bipolar|parity.shea',re.I)
hits=[x['path'] for x in t['tree'] if pat.search(x['path'])]
out=dict(head=d['sha'],live_receipt='sources/registry.receipt.json',reused_tree_path=str(p),reused_tree_sha256=H(p),reused_receipt_path=str(P/'registry-preprints-receipt.json'),reused_receipt_sha256=H(P/'registry-preprints-receipt.json'),tree_sha=t['sha'],truncated=False,path_hits=hits,scope='Path search only; hit bodies unread; no novelty clearance. Root tree truncated and unused. MathDB/Palomar inherited denials retained, no retries.')
(W/'registry-screen.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2)[:3500])
