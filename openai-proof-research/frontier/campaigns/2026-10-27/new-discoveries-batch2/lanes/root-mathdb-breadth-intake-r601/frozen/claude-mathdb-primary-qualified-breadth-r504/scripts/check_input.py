import json,sys
d=json.load(open(sys.argv[1],encoding='utf-8'));ids=json.load(open(sys.argv[2],encoding='utf-8'))['ids']
print(len(d), set(map(int,d))==set(ids), len(ids))
