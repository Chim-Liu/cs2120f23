def isEvenLen : String → Bool := λ s => s.length % 2 == 0
/- My version
def combine : Bool → Bool → Bool := λ a b => a && b
def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

def allEvenLengths (lst : List String) : Bool :=
  foldr (λ s acc => combine (isEvenLen s) acc) true lst

#eval allEvenLengths ["hello", "world"]
#eval allEvenLengths ["hello,", "lean"]
#eval allEvenLengths ["hi", "its ", "even", "length"]
-/

/-new version-/
def combine : String → Bool → Bool
| s, b => and (isEvenLen s) b

def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

#eval foldr combine true ["hello", "world"]
#eval foldr combine true ["hello,", "lean"]
#eval foldr combine true ["hi", "its ", "even", "length"]


def foldr_ {α : Type} : (α → α → α) → α → List α → α
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr_ op id t)

#eval foldr_ (Nat.add) 0 [1, 2, 3]
#eval foldr_ (Nat.mul) 1 [1, 2, 3]

/- What can go wrong
You can pass a non-identity element
-/

/- What rules must be enforced?
id is the identity element for op, op must be associative
( ∀(a:α), op a id = a (right identity) and
∀(a:α), op id a = a (left identity) ), then id is an identity element of op
-/

/- structure, monoid, (α : Type)
(op : α → α → α)
(id : α)
∀(a:α), op a id = a (right identity)
∀(a:α), op id a = a (left identity)
-/

structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀(a : α), op id a = a )
(right_id : ∀(a : α), op a id = a )

def a_monoid : my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry

#check my_monoid
#check a_monoid.op

/- Imply truth table
P | Q | P → Q
T | T | T
T | F | F
F | T | T
F | F | T -/

#check Empty

def e2e : Empty → Empty
| e => e

def n2e : Nat → Empty
| n => _

/- Type universals -/
inductive higher
| mk
    (α : Type)
