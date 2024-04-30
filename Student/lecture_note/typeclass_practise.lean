#reduce Nat.succ <$> [0,1,2]

universe u
inductive Box (α : Type)
| contents (a : α)
/-
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  /-- If `f : α → β` and `x : F α` then `f <$> x : F β`. -/
  map : {α β : Type u} → (α → β) → f α → f β
  /-- The special case `const a <$> x`, which can sometimes be implemented more
  efficiently. -/
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)
-/
def Box_map{α β:Type}:(α → β )→ Box α → Box β
|f, (Box.contents a)=> Box.contents (f a)

instance: Functor Box:=⟨box_map⟩
#reduce Nat.succ <$> (Box.contents 2)

#eval (λ s => s ++ "!") <$> (Box.contents "Hi")
