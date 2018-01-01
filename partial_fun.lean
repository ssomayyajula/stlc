def partial_fun (α β) := α → option β

universes u v
variables {α : Type u} {β : Type v}

def emptyf : partial_fun α β
| _ := none

instance : has_emptyc (partial_fun α β) :=
⟨emptyf⟩

variable [decidable_eq α]

-- Destructive addition to a context
def extend (f : partial_fun α β) (x : α) (y : β) : partial_fun α β
| x' := if x' = x then y else f x'

instance : has_insert (α × β) (partial_fun α β) :=
⟨λ ⟨a, b⟩ f, extend f a b⟩

lemma extend_eta (f : partial_fun α β) (x : α) (y : β) :
  extend f x y = λ x', if x' = x then y else f x' := rfl

lemma extend_same (f : partial_fun α β) (x : α) (y : β) : extend f x y x = y :=
by unfold extend; simp

lemma extend_diff (f : partial_fun α β) {x x' : α} (y : β) :
  x' ≠ x → extend f x y x' = f x' :=
by intro h; unfold extend; simp [h]