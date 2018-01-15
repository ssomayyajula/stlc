import .syntax .typing .partial_fun

-- Encodes an typechecking algorithm
/-instance {Γ : ctx} {e : term} {τ : type} : decidable (has_type_under Γ e τ) :=
begin
  induction e generalizing Γ τ,

  case term.unit
  { cases τ,
    { right, apply has_type_under.unit },
    { left, intro t, cases t } },

  case term.var x
  { by_cases (Γ x = some τ),
    { right, apply has_type_under.var, assumption },
    { left, intro t, cases t, contradiction } },
  
  case term.abs x τ' e ih
  { cases τ,
    case type.unit
    { left, intro t, cases t },

    case type.func τ'' τ
    { cases @ih (extend Γ x τ') τ,
      { left, intro t, cases t, contradiction },
      { by_cases (τ'' = τ') with h,
        { rw h, right, apply has_type_under.abs, assumption },
        { left, intro t, cases t, contradiction } } } },

  case term.app e₁ e₂ ih₁ ih₂
  { 
  }
end
-/

instance {α} {a : option α} : decidable (∃ b, a = some b) :=
begin
  cases a,
  left, intro h, cases h, contradiction,
  right, existsi a, refl
end

class inductive tdecidable (t : Prop) : Prop
| is_false : (t → false) → tdecidable
| is_true : t → tdecidable

instance infer {e : term} : ∀ {Γ : ctx}, tdecidable (∃ τ, has_type_under Γ e τ) := begin
  intro Γ,
  induction e generalizing Γ,

  case term.var x
  { by_cases (∃ τ, Γ x = some τ),
    
    right, cases h with τ h, existsi τ,
    apply has_type_under.var, assumption,

    left, intro t, cases t with τ t, cases t,
    let := forall_not_of_not_exists h τ,
    contradiction },

  case term.abs x τ e ih
  {
      cases @ih (extend Γ x τ) with h h,

      left, intro t, cases t with τ' t, cases t,
      let := forall_not_of_not_exists h τ'_1,
      contradiction,

      right, cases h with τ' t,
      existsi type.func τ τ',
      apply has_type_under.abs,
      assumption,
  },

  case term.app e₁ e₂ ih₁ ih₂
  { cases @ih₁ Γ with ih₁ ih₁',

    left, intro t, cases t with τ' t, cases t,
    let := forall_not_of_not_exists ih₁ (type.func τ τ'),
    contradiction,

    cases @ih₂ Γ with ih₂ ih₂',
    left, intro t, cases t with τ' t, cases t,
    let := forall_not_of_not_exists ih₂ τ,
    contradiction,

    --left,
    cases ih₁' with τ,
    cases τ,
    left, intro t, cases t with _ t, cases t with _ t, cases a, cases a_2, 
  },

  case term.unit
  {
      right, existsi type.unit, apply has_type_under.unit
  }
end
