# I181 analytic record: what is proved and what is not

No new graph, prism parameter, triple, attachment or population census
was tested. The only new enumeration is a formal segment-incidence
certificate on the abstract six-cycle patch; it tests no additional
embedded graph.

## Reduction of the patch

Label the common chord's endpoints `x,y` and the simple boundary cycle
`C=(x,a,b,y,d,c,x)`. Its alternating halves are

```text
A = {xa, by, dc},   B = {ab, yd, cx}.
```

Every vertex of `C` is internal and cubic. Within the two-face disk,
`x` and `y` have no other incident edge than the chord and their two
boundary edges. Each of `a,b,c,d` has exactly one external continuation
edge.

If a lost packing uses exactly `A` on `C`, degree two forces the chord
and all four external continuation edges. A helper whose overlay has `C`
as a whole alternating component must use exactly `B` on `C`, and the
same degree argument forces the same chord and continuation edges.

On the four continuation terminals, both prescribed local sets give the
same abstract routing:

```text
A + xy:   a-x-y-b   and   c-d
B + xy:   a-b       and   c-x-y-d.
```

Thus both route `a` to `b` and `c` to `d`. Replacing one local routing
by the other therefore preserves the components of every unchanged
external segment decomposition. Singleton segments, loops and parallel
two-edge components must be retained when segments are contracted; the
fresh topology certificate checks this formal incidence statement.

Consequently, for any actual cycle-free same-type helper `u` satisfying
the local prescription, `v=u triangle E(C)` automatically has the same
spanning degree pattern, endpoint pairing and component/acyclicity
status as `u`. The coordinate identity `p+u=q+v` is immediate because
both packings toggle exactly the edges of `C`.

## Why existence remains unpaid

The graph must contain an actual survivor packing using `B`, the chord
and the four continuation edges while omitting `A`, and belonging to one
of the eleven stipulated survivor fibres. Neither elevenfold
nonemptiness nor brace two-extendability prescribes this simultaneous
local set.

A global Hamiltonian completion of the lost toggle `q` has a
complementary perfect matching containing the three disjoint edges `A`.
That supplies one matching with a Hamiltonian complement, but its local
cycle restriction is the lost packing `q`, not a survivor helper. The
required extension is a controlled one: a perfect matching containing
`A` whose complement is still a single Hamiltonian cycle and whose local
restriction has one of the eleven surviving pairings.

Brace extension applies to two disjoint edges, not the three edges `A`.
The stipulated P4 theorem can prescribe one three-edge path such as
`c-x-y-d`, but it does not simultaneously prescribe the separate edge
`a-b`, the four continuation edges, a cut/survival condition, or the
resulting packing type. No graph reduction preserving all required
hypotheses and lifting an actual helper was found. D168's false
bidirectional shortcut is not revived.

E181 is therefore UNRESOLVED, with the missing condition isolated as the
controlled three-edge alternating-half extension above.
