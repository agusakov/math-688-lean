/- 28 Aug 2019 -/

/-
# Graph Theory
"geometry of position" - how things interact with each other.

## Definitions:
* A `graph` is a set of vertices `V` (usually finite), a set of edges `E`, 
  (usually finite), and a corresponding function that associates to each
  edge in `E` two (not necessarily distinct) vertices in `V`.

* A graph is called `simple` if it has no loops nor multiple edges connecting 
  two vertices.

These are some really unwieldy definitions and we're just gonna use definitions from mathlib.
-/
import data.fintype.basic
import data.sym2
import data.set.finite

universes u
variables (α : Type u)

structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)
-- add more introductory stuff here