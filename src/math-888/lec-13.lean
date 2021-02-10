/- 9 Mar 2020 -/
-- Cayley graphs
import data.fintype.basic
import data.sym2
import data.set.finite
import group_theory.subgroup
import linear_algebra.matrix
import data.rel

open finset
universes u v


@[ext]
structure digraph (V : Type u) :=
(adj : V → V → Prop) -- for labelled edges, do `V → V → set S` or w/e
(loopless : irreflexive adj . obviously)

@[ext]
structure labelled_digraph (V : Type u) (α : Type*) :=
(adj : V → V → set α)
--(loopless : irreflexive adj . obviously)

/--
Construct the simple graph induced by the given relation.  It
symmetrizes the relation and makes it irreflexive.
-/
def digraph.from_rel {V : Type u} (r : V → V → Prop) : digraph V :=
{ adj := λ a b, (a ≠ b) ∧ r a b,
  loopless := λ a ⟨hn, _⟩, hn rfl }

open_locale big_operators matrix
open finset matrix digraph

variables {α : Type u} [fintype α]
variables (R : Type v) [semiring R]

variables (Γ : digraph α) (R) [decidable_rel Γ.adj]

/-- `adj_matrix G R` is the matrix `A` such that `A i j = (1 : R)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adj_matrix : matrix α α R
| i j := if (Γ.adj i j) then 1 else 0

variables {G : Type u} [add_comm_group G] [fintype G]

/- Let `(G, +)` be a finite abelian group. Let `S` be a generating set of `G` such that `S = -S`,
i.e. if `g ∈ S` then `-g ∈ S`, and `0 ∉ S`. The Cayley graph of `G` w.r.t. `S` is the graph `Γ`
whose vertex set is `G` and where, if `x, y ∈ G`, `Γ.adj x y` if `x - y ∈ S`. -/
-- for `S` we have 
  -- `finset G`
  -- if `g ∈ S` then `-g ∈ S`
  -- need hypothesis that says that `subgroup.closure S = ⊤`
  -- `0 ∉ S`
-- `adj` is defined as
  -- λ a b, a - b ∈ S

def cayley_graph (S : set G) (h : add_subgroup.closure S = ⊤) (h2 : (0 : G) ∉ S) (h4 : ∀ (g ∈ S), -g ∈ S) : digraph G := 
{ adj := λ a b, a - b ∈ S,
  loopless := 
    begin
      intros x h3,
      simp at h3,
      apply h2,
      exact h3,
    end }

def labelled_cayley_graph (S : set G) [decidable_pred S] (h : add_subgroup.closure S = ⊤) (h2 : (0 : G) ∉ S) 
  (h4 : ∀ (g ∈ S), -g ∈ S) : labelled_digraph G S := 
{ adj := λ a b, if h3 : (a - b) ∈ S then {⟨a - b, h3⟩} else ∅} 