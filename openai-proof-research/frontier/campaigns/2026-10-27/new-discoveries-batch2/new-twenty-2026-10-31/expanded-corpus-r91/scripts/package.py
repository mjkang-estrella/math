import pathlib,zipfile,hashlib,json,datetime
D=pathlib.Path(__file__).resolve().parents[1]
readme='''Lean 4.34.1; mathlib expected revision d13f23b723b8a846827a245b89c10fc7d3f11612.
Endpoint Eventown372630.literal_source_refutation.
Only propext, Classical.choice, Quot.sound are allowed.
Source Conjecture 16: https://arxiv.org/html/2601.12613v1#S6
The semantic family consists of actual permutations; exact even orbit lengths define cycles.
No computed maximum-clique assertion is a formal premise.
Cached upstream oleans are trusted; no full upstream rebuild or source/olean attestation claimed.
Root acceptance and independent novelty/fidelity reviews remain outstanding; credit zero.
'''
(D/'formal/README.txt').write_text(readme)
with zipfile.ZipFile(D/'372630-lean-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in [D/'formal/Eventown.lean',D/'formal/Audit.lean',D/'formal/README.txt',D/'PROOF-372630.md']:z.write(p,p.name)
P=D/'packet-replay';P.mkdir(exist_ok=True)
with zipfile.ZipFile(D/'372630-lean-packet.zip') as z:z.extractall(P)
for p in ['Eventown.lean','Audit.lean']:assert (P/p).read_bytes()==(D/'formal'/p).read_bytes()
print('Source-only packet extracted and byte verified inside lane.')
