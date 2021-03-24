/- 4 Sep 2019 -/
-- walks, trails, paths, circuits, Eulerian graphs, connected
import walks

universes u

namespace simple_graph

namespace walk

variables {V : Type u} (G : simple_graph V)
variables [decidable_eq V] {G}

def adj.to_edge {u v : V} (h : G.adj u v) : sym2 V := ⟦(u, v)⟧

/-- The edge set of a walk is the finite set of edges it visits. -/
def edge_set : Π {u v : V}, G.walk u v → finset (sym2 V)
| u _ nil := ∅
| u v (cons h p) := insert (adj.to_edge h) p.edge_set

/-- A trail is a walk that visits each edge at most once. -/
def is_trail : Π {u v : V}, G.walk u v → Prop
| u v nil := true
| u v (cons h p) := p.is_trail ∧ ¬ (adj.to_edge h) ∈ p.edge_set

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

instance fdnjskfnds {G : simple_graph V} {x y : V} (z : V) (p : G.walk x y) : fintype {n : ℕ // p.get_vert n = z} :=
begin
  sorry,
end

def count' {G : simple_graph V} {x y : V} (z : V) (p : G.walk x y) : ℕ := fintype.card {n : ℕ // p.get_vert n = z}


-- basically need to show that, if there is some incoming edge to `v`, there is a corresponding outgoing edge from `v`
lemma cycle_even_outgoing_edges (G : simple_graph V) [∀ (v : V), decidable_pred (G.incidence_set v)] (v : V)
  (c : G.walk v v) (h : is_trail c) :
  ∀ (w : V), w ∈ c.support → even (finset.card (c.edge_set.filter (G.incidence_set w))) := 
begin
  intros w vmem,
  rw even,
  -- need to show the existence of path from default V to v, and then different path from v to default V
  -- and then show that the two edges incident with v are distinct?

  -- if w ∈ c.support then there's some edge containing it
  -- say w is the nth vertex
  -- maybe we can split the walk into v to w and w to v? at whatever index we choose
  rcases (mem_support_exists_get_vert c vmem) with ⟨j, hjl, hjeq⟩,
  -- so `v` is adjacent to vertices `j - 1` and `j + 1` 
  have h2 : w = v ∨ w ≠ v,
  tauto,
  cases h2 with hwveq hwvneq,
  sorry,

  have h3 : 0 < j,
  sorry,


  sorry,
end

-- goal : show that a connected graph is eulerian iff every vertex has even degree
theorem eulerian_iff_connected_even_deg (G : simple_graph V) [inhabited V] [decidable_rel G.adj] [is_connected G]: 
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