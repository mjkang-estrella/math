import json,hashlib,os,sys
lane=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
man=json.load(open(f'{lane}/manifest.json'))
fails=[]
for a in man['artifacts']:
    p=f"{lane}/{a['path']}"
    if not os.path.exists(p): fails.append(("missing",a['path'])); continue
    h=hashlib.sha256(open(p,'rb').read()).hexdigest()
    if h!=a['sha256']: fails.append(("hash",a['path']))
d=json.load(open(f'{lane}/screening/dispositions.json'))
s=json.load(open(f'{lane}/shortlist/shortlist.json'))
pr=json.load(open(f'{lane}/intake-proposals.json'))
if len(d['dispositions'])!=48: fails.append(("disp_count",len(d['dispositions'])))
if len(s['candidates'])!=10: fails.append(("short_count",len(s['candidates'])))
if len(pr['proposals'])!=48: fails.append(("prop_count",len(pr['proposals'])))
ids=[x['mathdb_id'] for x in d['dispositions']]
if len(set(ids))!=48: fails.append(("dup_ids",))
sl=set(c['mathdb_id'] for c in s['candidates'])
if not sl<=set(ids): fails.append(("shortlist_not_subset",))
# reverify witness artifact self-consistency: recompute one witness
def nim(S,N=600):
    g=[0]*(N+1)
    for n in range(1,N+1):
        sset={g[n-m] for m in S if m<=n}; i=0
        while i in sset: i+=1
        g[n]=i
    return g
w=json.load(open(f'{lane}/screening/witness-375237.json'))
if nim((1,3,5))[1:41]!=w['primary_witness']['g_1_40']: fails.append(("witness_recompute",))
# input bindings spot check
ib=json.load(open(f'{lane}/administrative/input-bindings.json'))
for b in ib['bindings'][:3]:
    h=hashlib.sha256(open(b['path'],'rb').read()).hexdigest()
    if h!=b['sha256']: fails.append(("input_binding",b['name']))
print("VERIFY", "FAIL:"+str(fails) if fails else "PASS", "| artifacts:",len(man['artifacts']),
      "| dispositions:",len(d['dispositions']),"| shortlist:",len(s['candidates']),
      "| proposals:",len(pr['proposals']))
sys.exit(1 if fails else 0)
