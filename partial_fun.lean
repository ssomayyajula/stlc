def partial_fun (α β) := α → option β

universes u v
variables {α : Type u} {β : Type v}

def emptyf : partial_fun α β
| _ := none

instance : has_emptyc (partial_fun α β) :=
⟨emptyf⟩

inductive dom (f : partial_fun α β) : set α
| intro (a) (b) : f a = some b → dom a

variable [decidable_eq α]

-- Destructive addition to a context
@[irreducible]
def extend (f : partial_fun α β) (x : α) (y : β) : partial_fun α β
| x' := if x' = x then y else f x'

instance : has_insert (α × β) (partial_fun α β) :=
⟨λ ⟨a, b⟩ f, extend f a b⟩

variable (f : partial_fun α β)

lemma extend_same (x : α) (y : β) : extend f x y x = y :=
by unfold extend; simp

lemma extend_diff {x x' : α} (y : β) :
  x' ≠ x → extend f x y x' = f x' :=
by intro h; unfold extend; simp [h]

lemma extend_comm {x₁ x₂ : α} (y₁ y₂ : β) : x₁ ≠ x₂ →
  extend (extend f x₁ y₁) x₂ y₂ = extend (extend f x₂ y₂) x₁ y₁ :=
begin
  intro h,
  apply funext,
  intro x,
  
  by_cases x = x₁ with h',
  simp [h', extend_same,
        extend_diff _ _ h],
  
  rw extend_diff _ _ h',
  by_cases x = x₂ with h'',
  
  simp [h'', extend_same],

  simp [extend_diff _ _ h',
        extend_diff _ _ h'']
end
