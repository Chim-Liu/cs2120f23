import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basic

/-!
binary relation on a type, α
- reflexive
- symmetric
- transitive
- equivalence (Core.lean)
- asymmetric
- antisymmetric
- closures
- inverse

- empty relation
- complete relation
- subrelation

binary relation from α → β, etc
- compose
- join

inverse image
-/

inductive Person : Type
| lu
| mary
| jane

open Person

def Likes : Person → Person → Prop :=
  λ p1 p2 =>
    (p1 = lu ∧ p2 = mary) ∨
    (p1 = mary ∧ p2 = lu)

#reduce Likes lu mary

#reduce Likes lu jane


example : Likes lu mary := Or.inl ⟨ rfl, rfl⟩

#reduce Likes lu jane

example : ¬ Likes lu jane :=
λ h : Likes lu jane => by
  unfold Likes at h
  cases h with
  | inl l => nomatch l.2
  | inr r => nomatch r.1

  /-
    cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
  -/

/-
order relations
- partial order: reflexive, antisymmetric, transitive
- poset: a set α along with a partial order on α
- total order: partial order ∧ ∀ a b, a ≤ b ∨ b ≤ a
-/

/-
functions
- a single-valued relation is a function

- domain of definition
- codomain
- domain
- range
- partial
- total

- identity function -- See Mathlib.Logic.Function.Basic

- one-to-one (vs many-to-one, injective)
- onto (surjective)
- bijective

- composition
- inverse
- etc
-/
def a_set: Set Nat:={1,2,3}
def b_set: Set Nat:={3, 4,5}
def a_set':Set Nat:={n:Nat| n=1 ∨ n=2 ∨ n=3}
example: 1 ∈ a_set :=by
  show a_set 1
  unfold a_set
  show 1=1 ∨ 1=2 ∨ 1=3
  exact Or.inl rfl

example: 3∈ a_set ∩ b_set:=by
  show 3∈a_set ∧ 3∈b_set
  exact⟨Or.inr (Or.inr rfl),Or.inl rfl⟩

example: 2∈ a_set ∪ b_set :=by
  show 2∈a_set∨2∈b_set
  exact Or.inl (Or.inr (Or.inl rfl))

example: 2∈a_set \ b_set:=⟨(Or.inr (Or.inl rfl)),(
  by
    intro h
    nomatch h)⟩
--??
example: 3∉ a_set\ b_set:=⟨(
  by
    intro h
    nomatch h),_⟩

#reduce Reflexive (@Eq Nat)
lemma eq_nat_is_refl:Reflexive (@Eq Nat):=by
  unfold Reflexive
  intro x
  exact rfl

lemma eq_nat_is_symm:Symmetric (@Eq Nat):=by
  unfold Symmetric
  intro x y
  intro hxy
  rw[hxy]

lemma eq_nat_is_trans:Transitive (@Eq Nat):=by
  unfold Transitive
  intro x y z
  intro hxy hyz
  rw[hxy,hyz]

theorem eq_nat_is_equiv:Equivalence (@Eq Nat):=
  Equivalence.mk @eq_nat_is_refl @eq_nat_is_symm @eq_nat_is_trans

def cong_mod_n:Nat→Nat→Nat→Prop:=λ n a b=> n%a=n%b

example: cong_mod_n 3 2 5 := rfl

lemma cong_nat_is_refl:∀(n:Nat),Symmetric (cong_mod_n n):=by
  intro n
  unfold Symmetric
  intros x y
  intro hxy
  unfold cong_mod_n
  unfold cong_mod_n at hxy
  rw [hxy]

def comp123: Set Nat:={1,2,3}ᶜ

#reduce comp123 4

example: 4∈ comp123:=by
  intro h
  cases h
  contradiction
  rename_i h
  cases h
  contradiction
  contradiction
/-
The power set of product set of s&t is the set of relations on s&t
-/
