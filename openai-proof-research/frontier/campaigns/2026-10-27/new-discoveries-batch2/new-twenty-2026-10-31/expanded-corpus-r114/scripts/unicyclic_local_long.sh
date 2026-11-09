for a in "5 24" "9 24" "5 40"; do python3 scripts/unicyclic_local.py $a 6000 77 3 | python3 -c "
import json,sys,collections;d=json.load(sys.stdin);p={int(a):b for a,b in d['parent'].items()}
ch=collections.Counter(p.values());print(d['k'],d['n'],d['best_signed_margin'],'children-of-cycle',[ch[i] for i in range(d['k'])],'depth>1 vertices',sum(1 for v in p.values() if v>=d['k']))"; done
