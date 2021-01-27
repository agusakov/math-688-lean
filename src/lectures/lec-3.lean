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

structure eulerian_circuit (v : V) :=
(w : G.walk v v) 
(is_trail : is_trail w)
(saturates : ↑w.edge_set = G.edge_set)

def is_eulerian {G : simple_graph V} {v : V} (w : G.walk v v) : Prop :=
  is_trail w ∧ ↑w.edge_set = G.edge_set

def eulerian_graph (G : simple_graph V) [inhabited V] : Prop := 
  ∃ (w : G.walk (default V) (default V)), is_trail w ∧ ↑w.edge_set = G.edge_set

variables [fintype V]

--lemma finite_of_exists_eulerian {v : V} (w : G.walk v v)

lemma incidence_subset_eulerian_edge_set (G : simple_graph V) [inhabited V] 
(w : G.walk (default V) (default V)) (h : is_eulerian w) :
  ∀ (v : V), G.incidence_set v ⊆ w.edge_set :=
begin
  intros v,
  unfold is_eulerian at h,
  cases h with hwt hwsat,
  rw hwsat,
  exact G.incidence_set_subset v,
end

lemma cycle_even_outgoing_edges (G : simple_graph V) [inhabited V] (c : G.walk (default V) (default V)) :
  ∀ (v : V), v ∈ c.support → even (finset.card ((G.incidence_set v) ∩ ↑(c.edge_set)).to_finset) :=
begin
  intros v vmem,
  sorry,
end

-- goal : show that a connected graph is eulerian iff every vertex has even degree
theorem eulerian_iff_connected_even_deg (G : simple_graph V) [inhabited V] [is_connected G]: 
  eulerian_graph G ↔ (∀ (v : V), even (G.degree v)) :=
begin
  split,
  intros h v,
  unfold even,
  unfold eulerian_graph at h,
  rcases h with ⟨w, hwt, hwsat⟩,
  sorry,
  sorry,
end


end walk 

end simple_graph