
def add: Nat → Nat → Nat
|Nat.zero, a => a
|(Nat.succ n'), a => Nat.succ (add n' a)

--Nat.zero = 0 Nat.succ = (n' + 1)

#eval add 2 3
/-def append:
-/
def mul: Nat → Nat → Nat
|_, 0=>0
|a, (b+1) => add (mul a b) a

#eval mul 3 4

def exp: Nat → Nat → Nat
|_, 0 => 1
|n, (m+1) => mul (exp n  m) n

#eval exp 2 5

def append{α :Type}: List α → List α → List α
|List.nil, a => a
/-|(List.cons h List.nil), a => List.cons h a-/
|(List.cons h t), a => List.cons h (append t a)



#eval append [1,2,3] [4,5,6]
