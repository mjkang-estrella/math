import json, sys, glob, os
G = sys.argv[1]
d = json.load(open(os.path.join(G, 'review.json')))
print('review.json OK; verdicts:', {k: v['verdict'] for k, v in d['verdicts'].items()}, d['overall_recommendation'])
recs = [json.load(open(f)) for f in sorted(glob.glob(os.path.join(G, 'receipts', '*.json')))]
print('receipts', len(recs), 'nonzero exits', [r['name'] for r in recs if r['exit_code'] != 0], 'max rss', max(r['peak_rss_kib'] for r in recs), 'max user', max(r['user_s'] for r in recs))
net = [json.load(open(f)) for f in sorted(glob.glob(os.path.join(G, 'net', 'f*', '*.receipt.json')))]
print('net receipts', len(net), 'statuses', sorted(set(str(r['status']) for r in net)))
