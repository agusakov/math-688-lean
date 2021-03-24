import linear_algebra.matrix
import data.rel
import combinatorics.simple_graph.basic

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `adj_matrix` is the adjacency matrix of a `simple_graph` with coefficients in a given semiring.

-/

open_locale big_operators matrix
open finset matrix simple_graph

universes u v
variables {α : Type u} [fintype α]
variables (R : Type v) [semiring R]

namespace simple_graph

variables (G : simple_graph α) (R) [decidable_rel G.adj]

def simple_graph_from_matrix (M : matrix α α R) (h : Mᵀ = M) : simple_graph α := 
{ adj := λ v w, M v w = 1 ∧ v ≠ w,
  sym := λ v w h2, by { rw [← transpose_apply M, h], exact ⟨h2.1, ne.symm h2.2⟩ },
  loopless := λ v h2, h2.2 rfl }

@[ext]
structure digraph (V : Type u) :=
(adj : V → V → Prop)
(loopless : irreflexive adj . obviously)

end simple_graph