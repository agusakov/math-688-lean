/- 10 Feb 2020 -/
-- srgs
-- box product
-- hamming graph
-- triangular graph
-- paley graph
import combinatorics.simple_graph.basic

universes u v
variables (V : Type u) {W : Type u}

namespace simple_graph

variables {V}


/-
The box product of `G : simple_graph V` and `H : simple_graph W` is a graph on `V × W` such that
`(x.1, w1)` is adjacent to `(y.1, y.2)` when `x.1 = y.1` and `H.adj w1 y.2` or `G.adj x.1 y.1` and `w1 = y.2`.
In other words, the vertices differ by one coordinate. 
-/
def box_product (G : simple_graph V) (H : simple_graph W) : simple_graph (V × W) := 
{ adj := λ x y, (x.1 = y.1 ∧ H.adj x.2 y.2) ∨ (G.adj x.1 y.1 ∧ x.2 = y.2),
  sym := λ x y h,
    begin
      cases h with hv hw,
      { left,
        exact ⟨eq.symm hv.1, (H.edge_symm x.2 y.2).1 hv.2⟩ },
      { right,
        exact ⟨(G.edge_symm x.1 y.1).1 hw.1, eq.symm hw.2⟩ },
    end,
  loopless := λ ⟨v, w⟩ h, 
    begin
      cases h with hw hv,
      { exact H.irrefl hw.2 },
      { exact G.irrefl hv.1 },
    end }

notation G ` □ ` := box_product G

variables (G : simple_graph V) [decidable_rel G.adj]


variables [decidable_eq V] [decidable_eq W]

instance decidable_rel_box_product (H : simple_graph W) [decidable_rel H.adj] : decidable_rel (G □ H).adj :=
λ _ _, or.decidable

variables [fintype V] [decidable_eq V]

/--
A graph is strongly regular with parameters `n k l m` if
 * its vertex set has cardinality `n`
 * it is regular with degree `k`
 * every pair of adjacent vertices has `l` common neighbors
 * every pair of nonadjacent vertices has `m` common neighbors
-/
structure is_SRG_of (n k l m : ℕ) : Prop :=
(card : fintype.card V = n)
(regular : G.is_regular_of_degree k)
(adj_common : ∀ (v w : V), G.adj v w → fintype.card (G.common_neighbors v w) = l)
(nadj_common : ∀ (v w : V), ¬ G.adj v w → fintype.card (G.common_neighbors v w) = m)

lemma hamming_srg : ((complete_graph V) □ (complete_graph V)).is_SRG_of ((fintype.card V)^2) (2*(fintype.card V - 1)) (fintype.card V - 2) 2 := 
begin
  sorry,
end

end simple_graph