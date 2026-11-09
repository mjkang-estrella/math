import json,pathlib,itertools
O=pathlib.Path(__file__).resolve().parent
n=4;spokes=[(i,9+i) for i in range(9)];assert len(set(sum(([a,b] for a,b in spokes),[])))==18 and len(spokes)>n+1
# Across either cut abcd has disjoint alphabets, so LCS with reversed opposite half is empty.
w='abcd';cuts=[(w[:2],w[2:]),(w[1:3],w[3:]+w[:1])];assert all(set(a).isdisjoint(b) for a,b in cuts)
# Reproduce only the numerical obstruction in published Lu-Yang-Zhang construction, p=4.
p=4; A=p; B=3*p//2; order=A+B*p;defect=3*A-2*A-B;assert order==28 and defect==-2
(O/'cheap-checks.json').write_text(json.dumps({'status':'PASS_UNCREDITED_SANITY_ONLY','spoke_matching':{'n':4,'edges':spokes,'size':9,'claimed_bound':5},'arbitrary_alphabet_word':{'word':w,'even_palindrome_lengths':[0,0],'claimed_minimum':2},'published_parity_construction':{'source':'https://arxiv.org/pdf/2009.12802','p':p,'order':order,'criterion_defect':defect,'independent_factor_exhaustion':False}},indent=2))
