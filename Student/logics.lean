example (P Q:Prop) : P ∧ Q→ Q∧P:=
λ (h:P∧ Q)=>⟨h.2, h.1⟩

example (P Q:Prop) : P ∧ Q→ Q∧P
|And.intro p q=>And.intro q p

example (P Q:Prop) : P ∧ Q→ Q∧P
|⟨p,q⟩ =>⟨q,p⟩

example (P Q:Prop) : P ∧ Q→ Q∨ P
|⟨p,q ⟩ => Or.inl q


example (P Q:Prop): P∨ Q→  Q∨ P
|Or.inl p=>Or.inr p
|Or.inr q=>Or.inl q

example: ∀ (P:Prop),¬¬P→ P:=
λ p nnp=>_

example(P:Prop):(P∨ ¬P)→ (¬¬P→P)
|pornp => match pornp with
  |Or.inl p=>λ _=>p
  |Or.inr np=>λ nnp=>nomatch (nnp np)

  #check Classical.em

example (P:Prop) :(¬¬P→P):=
match(Classical.em P) with
  |Or.inl p=>λ _=>p
  |Or.inr np=>λ _=>by contradiction

def on_not_eq_zero(n:Nat):n=1→ n≠ 0:=
λ h => match n with
|Nat.zero=> nomatch h
|Nat.succ n'=>λ k=>by
  rw [k] at h
  cases h

def on_not_eq_zero_1(n:Nat):n=1→ n≠ 0:=
λ (neq1:n=1)=>λ neq0=> by
rw [neq1] at neq0
cases neq0

#check 1=0
#check Eq 1 0
#check Eq.refl 1

def isEven (n:Nat):Prop :=n%2=0

#check isEven 0
#check isEven 1
#reduce isEven 0
#reduce isEven 3

example: ∀ (n:Nat),isEven n:= _

def zornz: ∀ (n:Nat),n=0 ∨ n≠ 0:=
λ n => match n with
|0=>(Or.inl (Eq.refl 0))--Eq.refl 0 = rfl
|(_+1)=>Or.inr λ h=>nomatch h

#reduce zornz 3

variable
  (P:Type)
  (Q:P→Prop)
  (R:Prop)
  (t:P)
#check P
#check Q

#check Q t
#check ∀ (p:P), Q p

#check ∀ (_:P), R

example: ∃ (p:P), Q p:=_
def exists_even_nat: ∃ (n:Nat),isEven n:=⟨2 , rfl⟩

example: ∃ (n:Nat), n≠0:=⟨5,_⟩
def foo: (∃ (n:Nat),isEven n)→ True
|⟨n',pf⟩=>_

#check Eq
#check Eq.refl 1
example: 1+1=2:=rfl


inductive IsEven:Nat→Prop
|zero_is_even:IsEven 0
| even_plus_2_even:∀ (n:Nat),IsEven n → IsEven (n+2)

open IsEven
example:IsEven 0:= zero_is_even
example:IsEven 4:= even_plus_2_even 2 (even_plus_2_even 0)--?
