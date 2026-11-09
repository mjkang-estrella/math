exec(open(__file__.replace('fetch_registry_body.py','fetch_review.py')).read().split('jobs=')[0])
jobs={'omega-redundant-leaf':'https://raw.githubusercontent.com/the-omega-institute/trureturing/97cf8943cd45cc04759f669df39ad38cf35b1649/D5/S3/Combinatorics/Graph/RedundantLeafMatching.lean'}
exec('def get'+open(__file__.replace('fetch_registry_body.py','fetch_review.py')).read().split('def get')[1])
