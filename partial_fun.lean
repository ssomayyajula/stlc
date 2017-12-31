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
| x' := if x = x' then y else f x'

instance : has_insert (α × β) (partial_fun α β) :=
⟨λ ⟨a, b⟩ f, extend f a b⟩
