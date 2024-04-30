/-Realize the function of MapReduce-/

--Version 1: add up numbers in list
def foldr':(Nat→ Nat→ Nat)→Nat → List Nat→ Nat
|_,id,[]=>id
|op,id,h::t=>op h (foldr' op id t)
#reduce foldr' Nat.add 0 [1,2,3,4,5]
#reduce foldr' Nat.mul 1 [1,2,3,4,5]

#reduce foldr' Nat.sub 0 [5,3,1]

/-fold_str takes a list of string returns single string in which
all the given string are using string.append-/


def foldr_str:(String→ String→ String)→ String → List String→ String
|_,id,[]=>id
|op,id,h::t=>op h (foldr_str op id t)

#eval foldr_str String.append "" ["Hello,","World"]


def fold_all{α :Type}:(α → α→ α)→ α → List α→ α
|_,id,[]=>id
|op,id,h::t=>op h (fold_all op id t)

#eval fold_all String.append "" ["Hello,","World"]


/-reduce a list of string to a boolean
true if all string in list have even length-/
def isEVenlen: String→ Bool:= λ s=> s.length%2 == 0
def fold_r{α β:Type}:(α → β → β)→ β  → List α → β
|_,id,[]=>id
|op ,id,h::t=>op h (fold_r op id t)
def combine: String → Bool→ Bool:= λ S B => isEVenlen S && B

#eval fold_r combine True ["Hello,", "World,"]
