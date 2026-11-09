import json,sys
print(json.dumps(json.load(open(sys.argv[1],encoding='utf-8'))['disposition_counts'],indent=0,sort_keys=True))
