"""Reclassify original counter increment sites; no algorithm repair or new inputs."""
import ast
import contextlib
import io

src = open('research/artifacts/W019-smart-original-unverified.py').read()
tree = ast.parse(src)


class CounterSplit(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        prior = getattr(self, 'owner', None)
        self.owner = node.name
        self.generic_visit(node)
        self.owner = prior
        return node

    def visit_AugAssign(self, node):
        self.generic_visit(node)
        if ast.unparse(node.target) == "OPS['point_add']":
            label = 'affine' if self.owner == 'aff_add' else 'jacobian'
            extra = ast.parse("SPLIT[%r] += 1" % label).body[0]
            return [node, ast.copy_location(extra, node)]
        return node


tree = ast.fix_missing_locations(CounterSplit().visit(tree))
ns = {'SPLIT': {'affine': 0, 'jacobian': 0}}
with contextlib.redirect_stdout(io.StringIO()) as out:
    exec(compile(tree, '<counter-audit>', 'exec'), ns)
print('original_demo_event_split', ns['SPLIT'], 'original_mixed_total', ns['OPS']['point_add'])
assert sum(ns['SPLIT'].values()) == ns['OPS']['point_add'] == 408
for line in out.getvalue().splitlines():
    if line.startswith('ORD'):
        print(line)
