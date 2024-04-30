#check False.rec


#check Bool.rec


#check Nat.rec
#check List.reverse_cons
inductive Tree(α:Type) where
|empty :Tree α
|node (a:α) (l r: Tree α)
#check Tree.rec
example :∀ (b:Bool),!!b=b:=
by
  intros b
  induction b
  repeat {rfl}

#check Tree.rec

def fact:Nat→Nat:=_

def fact_0:=1

def fact_succ:(n:Nat)→(fact_n:Nat)→Nat
|n,fact_n=> fact_n *(n+1)

#eval fact_succ 5 234
#reduce (Nat.rec fact_0 fact_succ : Nat→Nat) 5
#reduce (Nat.rec fact_0 fact_succ : Nat→Nat)


def list_step{α:Type}:α →List α→Nat→Nat:=_

#reduce (List.rec 0 list_step _)
/-

--attribute
symetric
+reflexive
+transitive
+equivalence relation
+partial order
+antisymetric
+assymetric: total order, single valued


∀ (r:α→α→Prop),∀(a b:α), r a b→r b a

def isSyrn(r:α→α→Prop):∀(a b:α),r a b→r b a
-/
def lsaSym(r:α→α→Prop):=∀(a b:α),r a b→¬(r b a)
def antiSym(r:α→α→Prop):=∀(a b:α),r a b→r b a→a=b

def isSyrn(r:α→α→Prop):=∀(a b:α),r a b→r b a
def isRefl(r:α→α→Prop):=∀(a:α),r a a
def isTrans(r:α→α→Prop):=∀(a b c:α), r a b→r b c→r a c
def isEquiv(r:α→α→Prop):=(isSyrn r)∧(isRefl r)∧(isTrans r)

--single_valued r:=∀ x,y,z: r x y→ r x z→ y=z one end
--injective r:=single_valued r ∧ ∀ a b c,r a c→r b c→a=b one start

inductive Person:Type
|lu
|mary
|jane

open Person
def Likes: Person→Person→Prop:=
λ p1 p2 =>(p1=lu ∧ p2=mary)∨
(p1=mary ∧ p2=lu)

example: Likes lu mary:=Or.inl ⟨rfl,rfl⟩

#reduce Likes lu jane

example: ¬ Likes lu jane:=
λ h:Likes lu jane => by
 cases h with
 nomatch h.2

example: ¬ Likes lu jane:=
λ h:Likes lu jane => by
 unfold Likes at h
 cases h with
 | Or.inl l => nomatch l.2
 | Or.inr r => nomatch r.1

/-
dod: domain of definition--x
codomain--y

total: F is total iff:
∀ a∈f.dod, ∃ b∈codomain, st.
r a b

surjective/onto: F is surjective iff:
∀ b∈f.codomain, ∃ a∈f.dod, st.
r a b
-/
