from pathlib import Path
import json
r=Path(__file__).resolve().parent;i=json.loads((r/'endpoint.json').read_text())['last_id']
p=r/'endpoint-r8.py';p.write_text(p.read_text().replace('simp [MaskRUP.bits] at hn','simp [MaskRUP.bits, MaskChain.maskR8_{idx}] at hn'))
for p in [r/'packet/src/EndpointR8.lean',r/'optimized-extracted/src/EndpointR8.lean']:
 p.write_text(p.read_text().replace('simp [MaskRUP.bits] at hn',f'simp [MaskRUP.bits, MaskChain.maskR8_{i}] at hn'))
