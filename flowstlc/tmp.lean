import Lean.Data.RBMap

variable {α β σ : Type}
variable (cmp : α → α → Ordering)
variable (m : Lean.RBMap α β cmp)

#check m.fold
#check m.insert
#check m.find?
#check m.toList

def sample : Lean.RBMap Nat Nat compare :=
  ((Lean.RBMap.empty.insert 2 20).insert 1 10).insert 3 30

def rebuild : Lean.RBMap Nat Nat compare :=
  sample.fold (fun acc k v => acc.insert k v) Lean.RBMap.empty

#reduce sample = rebuild
