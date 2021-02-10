/- 10 Feb 2020 -/
-- srgs
-- box product
-- hamming graph
-- triangular graph
-- paley graph
import combinatorics.simple_graph.basic

universes u v
variables (V : Type u) (W : Type u)

namespace simple_graph

def box_product (G : simple_graph V) (H : simple_graph W) : simple_graph (V × W) := 
{ adj := λ ⟨v1, w1⟩ ⟨v2, w2⟩, (v1 = v2 ∧ H.adj w1 w2) ∨ (G.adj v1 v2 ∧ w1 = w2),
  sym := λ ⟨v1, w1⟩ ⟨v2, w2⟩ h,
    begin
      cases h with hv hw,
      { left,
        exact ⟨eq.symm hv.1, (H.edge_symm w1 w2).1 hv.2⟩ },
      { right,
        exact ⟨(G.edge_symm v1 v2).1 hw.1, eq.symm hw.2⟩ },
    end,
  loopless := λ ⟨v, w⟩ h, 
    begin
      cases h with hw hv,
      { exact H.irrefl hw.2 },
      { exact G.irrefl hv.1 },
    end }

end simple_graph