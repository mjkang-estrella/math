import json, sys
R = json.load(open(sys.argv[1], encoding='utf-8'))
a, b = int(sys.argv[2]), int(sys.argv[3])
for r in R[a:b]:
    x = r['record']
    print('=== %d | %s | %s:%d | compl=%s | src=%s | %s | refs=%s | sols=%s' % (x['mathdb_id'], x.get('title'), r['chunk'][-10:], r['line'], x.get('statement_completeness'), x.get('source_name'), x.get('source_url'), len(x.get('references') or []), x.get('solution_count')))
    print(x.get('statement'))
