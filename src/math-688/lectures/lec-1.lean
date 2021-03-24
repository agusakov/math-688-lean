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

universes u v
variables (α : Type u)

structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)
-- add more introductory stuff here

structure graph (V : Type u) (E : Type v) :=
(func : E → sym2 V)
-- try finsum API

-- V → E → ℕ, edges sum to 2
-- V → list E
structure graph2 (V : Type u) (E : Type v) :=
(func : V → list E)
/-
Pros: 
  * incidence between two edges `e f` is just `∃ (v : V), e ∈ func v ∧ f ∈ func v`
Cons:
  * neighborhood of vertex `v` is very awkward to define
-/

-- E → list V
structure graph3 (V : Type u) (E : Type v) :=
(func : E → list V)
/-
Pros:
  * easy to do hypergraphs, digraphs, multigraphs from here
  * similar to the definition from lecture
  * incidence between two edges `e f` is just `func e ∩ func f ≠ ∅`
Cons:
  * undirected graphs need to be defined as quotient type i think? on ordering of list V
  * neighborhood of vertex `v` very unwieldy, have to define it as union of `func e` over all 
      `e` such that `v ∈ func e`
  * what happens if you have empty list or list with one vertex? that shouldn't be allowed
-/