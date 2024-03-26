inductive BobStudiesAtUVa
| attendsClasses
| paidTuition

inductive MaryStudiesAtUVa
| attendsClasses
| paidTuition
inductive MarkoStudiesAtUVa

def neg(α:Type):= α → Empty
example : neg MarkoStudiesAtUVa :=λ m : MarkoStudiesAtUVa => nomatch m



inductive BobStudiesAtUVaAndMaryStudiesAtUVa
| and (b:BobStudiesAtUVa)(m:MaryStudiesAtUVa)

def b : BobStudiesAtUVa:= BobStudiesAtUVa.paidTuition
def m : MaryStudiesAtUVa:= MaryStudiesAtUVa.paidTuition

example: BobStudiesAtUVaAndMaryStudiesAtUVa:= BobStudiesAtUVaAndMaryStudiesAtUVa.and b m

inductive BobStudiesAtUVaOrMaryStudiesAtUVa
| left (b:BobStudiesAtUVa)
| right (m:MaryStudiesAtUVa)

example: BobStudiesAtUVaOrMaryStudiesAtUVa:= BobStudiesAtUVaOrMaryStudiesAtUVa.left b

inductive MyAnd (α β:Type):Type
|mk (α:α ) (b:β )

example: MyAnd BobStudiesAtUVa MaryStudiesAtUVa:= MyAnd.mk b m

inductive MyOr(α β :Type):Type
|inl (a:α )
|inr (b:β )
example: MyOr BobStudiesAtUVa MaryStudiesAtUVa:= MyOr.inl b
example: MyOr BobStudiesAtUVa MaryStudiesAtUVa:= MyOr.inr m

def MyNot(α :Type):= α →  Empty

example: MyNot BobStudiesAtUVa:= λ b=> _

example: MyNot MarkoStudiesAtUVa:= λ m=> nomatch m


#check (@Prod)

example: Prod BobStudiesAtUVa MaryStudiesAtUVa:= Prod.mk b m

example: BobStudiesAtUVa × MaryStudiesAtUVa → BobStudiesAtUVa:= λ p => p.fst
example: BobStudiesAtUVa × MaryStudiesAtUVa → MaryStudiesAtUVa:= λ p => p.2

#check(@Sum)

example: Sum BobStudiesAtUVa MarkoStudiesAtUVa:= Sum.inl b
example: BobStudiesAtUVa ⊕ MarkoStudiesAtUVa:= Sum.inr _--no proof.


example: BobStudiesAtUVa ⊕ MarkoStudiesAtUVa → BobStudiesAtUVa
|(Sum.inl l)=>l
|(Sum.inr r)=> nomatch r


#check(@neg)
example: neg MarkoStudiesAtUVa:= λ p: MarkoStudiesAtUVa=>nomatch p

example: neg (MaryStudiesAtUVa× MarkoStudiesAtUVa):=λ p=> nomatch p.2


inductive B: Prop
|paid
|classes

inductive M: Prop
|paid
|classes

inductive K: Prop

#check(@And)
example:And B M:= And.intro B.paid M.classes
example:B ∧ M:= And.intro B.paid M.classes

theorem b_and_m_true : B∧ M := And.intro B.paid M.classes
example: B∧ M := ⟨ B.paid, M.classes⟩
example: B∧ M→ M := λ p=>p.right



def foo: B∧ Not K:= ⟨ B.paid, λ k => nomatch k ⟩
example: B∧ ¬ K:=foo
example: B∧ Not K:= ⟨ B.paid, λ k => nomatch k ⟩


example: B∨ K:= Or.inl B.paid
example: B∨ K→ B:= λ bork=> match bork with
| Or.inl b=> b
| Or.inr k=> nomatch k

example:
∀ (Raining Sprinkling Wet:Prop),
  (Raining ∨ Sprinkling)→
  (Raining→ Wet)→
  (Sprinkling→ Wet)→
  Wet:=λ _ _ _ rors rw sp=> match rors with
  | Or.inl R=>rw R
  | Or.inr S=>sp S


def notK: ¬K:=λ k=> nomatch k
example(P:Prop): ¬P → P→ False:=λ np p =>np p

example (P:Prop):¬¬P→ P
| nnp=>_

example (P:Prop):(P∨ ¬P)→ (¬¬P→ P)
| pornp=> match pornp with
  | Or.inl p=>λ _=>p
  | Or.inr np=>λ nnp=> nomatch (nnp np)

--∀ (P:Prop), P∨ ¬P
