from fetch import *
todo=[('loop-journal.pdf','https://projecteuclid.org/journals/rocky-mountain-journal-of-mathematics/volume-36/issue-2/Moufang-loops-that-share-associator-and-three-quarters-of-their/10.1216/rmjm/1181069461.pdf'),('loop-thesis.pdf','https://www.cs.du.edu/~petr/data/papers/connections_between_codes_groups_and_loops.pdf'),('loop-code-later.pdf','https://cs.du.edu/~petr/data/papers/code_loops_in_dimension_at_most_8.pdf'),('closest-groups.pdf','https://cs.du.edu/~petr/data/papers/closest_multiplication_tables_of_groups.pdf')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,todo):print(v,flush=True)
