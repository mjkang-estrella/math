
from itertools import product
import time
#Generate all oriented paths of n vertices. A sequence of length n-1 consisting of "1"s and "-1"s represents the sequence of edges, where "1" means the edge is from the left to the right, and "-1" means the other direction.
def generate_sequences(n):
    seq_length = n - 1
    return product([1, -1], repeat=seq_length) if seq_length > 0 else []
# Calculate the isomorphic digraph of an oriented path.
def iso(path_a):
    return tuple(-path_a[len(path_a)-1-i] for i in range(len(path_a)))
#Check whether an oriented path is symmetric
def sym(path_a):
    return all(path_a[i] + path_a[len(path_a)-1-i] == 0 for i in range(len(path_a)//2))
#Fix an oriented path, and integers i and k, calculate the composition corresponding to p_{i,i+k-1}. "td_values" and "prefix_gt" are from "path".
def one_composition(path, td_values, prefix_gt, i, k):
    n_vertices = len(td_values)
    if i == 0:
        td_p_i = path[k - 1]
    elif i == n_vertices - k:
        td_p_i = -path[n_vertices - k - 1]
    else:
        td_p_i = path[i + k - 1] - path[i - 1]
    start, end = i, i + k - 1
    t = td_p_i
    ones_before_k = prefix_gt[t][start] + (prefix_gt[t][n_vertices] - prefix_gt[t][end + 1])
    ones_after_k = n_vertices - k - ones_before_k
    return tuple([1] * ones_before_k + [k] + [1] * ones_after_k)
def compositions_with_ones(path):
    n_vertices = len(path) + 1
    td_values = [0] * n_vertices #We use td_values to record the total degree of vertices.
    if n_vertices >= 1:
        td_values[0] = path[0]
    if n_vertices >= 2:
        td_values[-1] = -path[-1]
    for j in range(1, n_vertices - 1):
        td_values[j] = path[j] - path[j - 1]

    prefix_gt = {}
    for t in [-2, -1, 0, 1, 2]:
        prefix = [0] * (n_vertices + 1)
        for j in range(n_vertices):
            prefix[j + 1] = prefix[j] + (1 if td_values[j] > t else 0)
        prefix_gt[t] = prefix #prefix_gt[t][i] is the number of vertices whose total degrees are larger than t and whose indices are smaller than i. We use prefix_gt to reduce the number of comparisons.
    result = []
    for k in range(2, n_vertices):
    #Fix an oriented path and an integer k, get the list k_compositions whose i-th element is the composition corresponding to p_{i,i+k-1}.
        max_i = n_vertices - k + 1
        k_compositions = []
        for i in range(max_i):
            k_compositions.append(one_composition(path, td_values, prefix_gt, i, k))
        result.append(tuple(sorted(k_compositions)))
    return tuple(result)

#When n is odd, delete the isomorphic oriented paths and check whether there are non-isomorphic oriented paths with the same result of "compositions_with_ones". For a non-symmetric oriented path D, we keep either D or iso(D).
def process_sequences(sequences, check_symmetry):
    processed = set()#Collect the sequences we have
    seen_results = set()
    for seq in sequences:
        seq_tuple = tuple(seq)
        #We have proved for symmetric oriented paths, so we skip them.
        if check_symmetry and sym(seq_tuple):
            continue
        if seq_tuple in processed:
            continue
        result = compositions_with_ones(seq_tuple)
        if result in seen_results:
            return False
        seen_results.add(result)
        processed.add(seq_tuple)
        processed.add(iso(seq_tuple))
    return True

def main(n):
    print(f"Begin for oriented paths of {n} vertices")
    if n <= 2:
        print(f"There is only one oriented path of {n} vertices")
        return True
    if n % 2 == 1:
        sequences = generate_sequences(n)
        if not process_sequences(sequences, check_symmetry=True):
            print(f"Failed. This method can not distinguish oriented paths of {n} vertices")
            return False
    else:#When n is even, there are an odd number of edges, and we require the middle edge to go from left to right to avoid isomorphism.
        i = (n-2) // 2
        pre_sequences = list(product([1, -1], repeat=i))
        post_sequences = list(product([1, -1], repeat=i))
        seen_results = set()
        for pre in pre_sequences:
            for post in post_sequences:
                seq_tuple = pre + (1,) + post
                result = compositions_with_ones(seq_tuple)
                if result in seen_results:
                    print(f"Failed. This method can not distinguish oriented paths of {n} vertices")
                    return False
                seen_results.add(result)
    print(f"Success! This method can distinguish oriented paths of {n} vertices.")
    return True
