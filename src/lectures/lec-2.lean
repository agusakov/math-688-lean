/- 30 Aug 2019 -/
-- degree
-- incidence matrix
-- adjacency matrix

/-
## Definitions:
* A sequence of nonnegative integers is called `graphic` if it is the degree
  sequence of a simple graph.

how does one write dn where n is a subscript?

Havel-Hakimi Theorem: Let d_1 ≥ d_2 ≥ ... ≥ d_n ≥ 0 be a (finite) sequence of 
nonnegative integers. The sequence is graphic iff the sequence 
  d_2 - 1, ... , d_(t + 1) - 1, d_(t + 2), ... , d_n, where t = d_1, is graphic.


Let 0 ≤ d_1 ≤ d_2 ≤ ... ≤ d_n be a (finite) sequence of 
nonnegative integers. The sequence is graphic iff the sequence 
  d_2 - 1, ... , d_(t + 1) - 1, d_(t + 2), ... , d_n, where t = d_1 is graphic.
-/

import data.list.sort
import combinatorics.simple_graph.basic

universe u
variables (V : Type u)

-- what type should i use?
  -- `list.sorted` or `list.pairwise`
-- i think i can just use nat since that includes zero

-- oh god i need some kind of counter? or index
-- copy over the sequence except erase largest element and 
  -- subtract one from the n next largest elements
def sub_one_n_times (n : ℕ) (l : list ℕ) : list ℕ :=
(l.take n).map (nat.pred) ++ l.drop n

-- in pseudocode,
-- a sequence D is graphic if degree defines inj function from G to D
  -- does this make sense

variables (l : list ℕ) [l.sorted (≤)]  -- nICE
variables (G : simple_graph V) [decidable_eq V] (v w x y : V) 
variables (h1 : G.adj v w) (h2 : G.adj x y) (hn1 : ¬ G.adj v x) (hn2 : ¬ G.adj w y)

def new_graph : simple_graph V := 
{ adj := λ a b, if (((a = v) ∧ (b = w)) ∨ ((a = v) ∧ (b = x)) ∨ (((a = w) ∧ (b = y)) ∨ ((a = x) ∧ (b = y)))) then ¬ G.adj a b 
                else G.adj a b, 
  -- there's gotta be a better way of doing this
  sym := λ a b,
  begin
    simp,
    intros h,
    sorry,
  end,
  loopless := sorry, }

/-def new_graph : simple_graph V := 
{ adj := λ a b, if ((a ≠ v) ∧ (a ≠ w)) ∨ ((b ≠ x) ∧ (b ≠ y)) then G.adj a b 
                else ¬ G.adj a b, 
  -- there's gotta be a better way of doing this
  sym := λ a b,
  begin
    simp,
    intros h,
  end,
  loopless := _ }-/

-- okay shit this is gonna be annoying

-- going to need to show that the max degree is le the number of remaining vertices

-- sequence D is graphic if ∃ (G : simple_graph V), D is deg seq for G

-- for proof, need to define swapping edge algo
  -- BUT FIRST we need to define edge deletion lmao