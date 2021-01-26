/- 4 Sep 2019 -/
-- walks, trails, paths, circuits, Eulerian graphs, connected
import walks

universes u

namespace simple_graph

namespace walk

variables {V : Type u} (G : simple_graph V)

/-- A walk is a sequence of incident edges in a graph, represented here as a sequence of adjacent
vertices. -/
inductive walk' : V → V → Type u
| nil {u : V} : walk' u u
| cons {u v w : V} (h : G.adj u v) (p : walk' v w) : walk' u w

variables [decidable_eq V] {G}

/-- The edge set of a walk is the finite set of edges it visits. -/
def edge_set : Π {u v : V}, G.walk u v → finset (sym2 V)
| u _ nil := ∅
| u v (cons h p) := insert ⟦(u, v)⟧ p.edge_set

/-- A trail is a walk that visits each edge at most once. -/
def is_trail : Π {u v : V}, G.walk u v → Prop
| u v nil := true
| u v (cons h p) := p.is_trail ∧ ¬ ⟦(u, v)⟧ ∈ p.edge_set



end walk 

end simple_graph