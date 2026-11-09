import sys, json, re
pats = ['331483','331822','326025','322876','323602','372424','372555','372565','372715','372827','372828','372834','372924','373059','373261','373329','373480','373637','373706','373718',
 '1510.00269','1511.05434','1307.8216','1201.4326','1206.0803','2601.03363','2601.09551','2601.09910','2601.16161','2601.20500','2601.20574','2602.03016','2602.08738','2602.19293','2602.23066','2603.06692','2603.15536','2603.18253','2603.18674',
 'halin','tone','isolation','cooperrowland','rowland','whitehead','automorphicconj','fourparts','biregular','higgins','oddcycle','alontarsi','latintrade','pseudoline','derangement','kronecker','ghost','hickingbotham','treechild','keevash','crouzeix','cylinder','directions','tablea','corner','excedance','gamma']
out = {}
for fn in sys.argv[1:]:
    d = json.load(open(fn))
    paths = [t['path'] for t in d.get('tree', [])]
    hits = {}
    for p in paths:
        q = re.sub(r'[^a-z0-9.]', '', p.lower())
        for k in pats:
            if k in q: hits.setdefault(k, []).append(p)
    out[fn] = {'paths': len(paths), 'truncated': d.get('truncated'), 'hits': {k: v[:8] for k, v in hits.items()}, 'hitcounts': {k: len(v) for k, v in hits.items()}}
print(json.dumps(out, indent=1))
