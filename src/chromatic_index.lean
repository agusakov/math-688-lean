import combinatorics.simple_graph.basic

namespace simple_graph
universes u v
variables {V : Type u} (G : simple_graph V)

def incident (e f : sym2 V) : Prop := ∃ (v : V), v ∈ e ∧ v ∈ f

@[ext]
structure edge_coloring (β : Type v) :=
(color : G.edge_set → β)
(valid : ∀ e f ∈ G.edge_set, incident e f → color e ≠ color f) --need incidence jesus

end simple_graph
