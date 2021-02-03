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
import data.multiset.sort

universe u
variables (V : Type u) [fintype V]

-- what type should i use?
  -- `list.sorted` or `list.pairwise`
-- i think i can just use nat since that includes zero

-- oh god i need some kind of counter? or index
-- copy over the sequence except erase largest element and 
  -- subtract one from the n next largest elements
def sub_one_n_times' (n : ℕ) (l : list ℕ) : list ℕ :=
(l.take n).map (nat.pred) ++ l.drop n
-- this one works i think, but ordering does matter

/-def list.pos_filter (l : list ℕ) : list ℕ := l.filter (λ n, 0 < n)
-- this probably already exists, just don't feel like looking it up

def n_pos_list_check (n : ℕ) (l : list ℕ) : Prop := n ≤ l.pos_filter.length-/

-- def nth_is_pos (n : ℕ) (l : list ℕ) [l.sorted (≤)] : Prop := 0 < (l.nth n)
-- bad

def sub_one_n_times (n : ℕ) (l : list ℕ) (h : l.sorted (≥)) : option (list ℕ) := if n ≤ (l.filter (λ n, 0 < n)).length then sub_one_n_times' n l else none

def havel_hakimi' (l : list ℕ) (h : l.sorted (≥)) : option (list ℕ) := sub_one_n_times l.head l.tail h.tail

-- also need check for all 0's

-- ideas for degree sequence
  -- multiset of vertices, take the image
  -- `multiset.sort` to get sorted list
variables {V}

def simple_graph.degree_multiset (G : simple_graph V) [decidable_rel G.adj] : multiset ℕ := finset.univ.val.map (λ v, G.degree v)

def simple_graph.degree_sequence (G : simple_graph V) [decidable_rel G.adj] : list ℕ := (finset.univ.val.map (λ v, G.degree v)).sort (≥)

variables (l : list ℕ) [l.sorted (≤)] 

-- in pseudocode,
-- a multiset ℕ is graphic if it is the degree sequence of some graph `G`
def graphic (s : multiset ℕ) : Prop := ∃ (G : simple_graph V) [decidable_rel G.adj], by exactI s = G.degree_multiset

-- a sorted list is graphic if blah blah
def graphic' (l : list ℕ) [l.sorted (≤)] : Prop := ∃ (G : simple_graph V) [decidable_rel G.adj], by exactI l = G.degree_sequence



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