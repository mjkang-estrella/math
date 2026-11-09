"""Print a heapsmany spec string: all nodes of star graphs with given arm triples."""
import sys

arms_list = [tuple(int(x) for x in a.split(',')) for a in sys.argv[1].split(';')]
items = []
for arms in arms_list:
    n = 1 + sum(arms)
    spec = 'star:' + ','.join(map(str, arms))
    for node in range(n):
        items.append(f'{spec}/{node}')
print(';'.join(items))
