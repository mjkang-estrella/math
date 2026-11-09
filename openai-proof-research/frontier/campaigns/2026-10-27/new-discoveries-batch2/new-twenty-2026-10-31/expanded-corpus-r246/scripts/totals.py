import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
for key,field in [('matching','pairs'),('matching-deep','sampled_pairs'),('cycles','tested_trianglefree_circulants'),('cycles-deep','tested_trianglefree_circulants'),('labels','permutations')]:
 rows=json.loads((D/f'{key}-coverage.json').read_text());print(key,'rows',len(rows),'total',sum(x[field] for x in rows))
print('source receipts',len(list((D/'sources').glob('*.receipt.json'))))
