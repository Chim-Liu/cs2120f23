/-reduce a list of string to a boolean
true if all string in list have even length-/
def isEVenlen: String→ Bool:= λ s=> s.length%2 == 0
def fold_r{α β:Type}:(α → β → β)→ β  → List α → β
|_,id,[]=>id
|op ,id,h::t=>op h (fold_r op id t)
def combine: String → Bool→ Bool:= λ S B => isEVenlen S && B

#eval fold_r combine True ["Hello,", "World,"]
#eval fold_r combine True ["Hello,", "World"]
#reduce fold_r combine true ["", "", ""] --should be true
