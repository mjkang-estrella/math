import sys, random
sys.path.insert(0, 'scripts')
import riordan, riordan_fast
random.seed(1)
for trial in range(300):
    n = random.choice([8, 16, 32, 40, 64])
    a = [1] + [random.randint(0, 1) for _ in range(n)]
    b = riordan.bell_matrix(a, n - 1)
    R = riordan_fast.rows_from_a(a, n - 1)
    for i in range(n - 1):
        assert all(((R[i] >> j) & 1) == b[i][j] for j in range(i + 1)), (n, i)
    A1 = riordan.graph(a, n); A2 = riordan_fast.adjacency(R, n)
    assert A1 == A2
    assert riordan.diameter(A1, n) == riordan_fast.ecc_all(A2, n, 10**9)
print('crosscheck ok: 300 random A-sequences, Bell rows, adjacency and diameter agree')
