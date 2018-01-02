/-
Soundness is typically proven by establishing progress and preservation
-/

import .typing .semantics

-- Hack: need to state Γ = ∅ since it will refuse to do induction directly on ∣- e : τ
lemma progress {e : term} {τ : type} {Γ : ctx} :
  Γ = emptyf → well_typed_under Γ e τ → is_value e ∨ ∃ e', e ⇝ e' :=
begin
  intros empty h,
  
  -- By induction on the typing judgment
  induction h,
  
  -- Impossible, variables cannot be typed in ∅
  case well_typed_under.var _ _ _ h
  { rw empty at h, contradiction },
  
  -- Unit and abstractions are trivially values
  case well_typed_under.unit
  { apply or.inl, apply is_value.unit },
  case well_typed_under.abs
  { apply or.inl, apply is_value.abs },

  -- Applications always evaluate
  case well_typed_under.app _ e₁ e₂ _ _ te₁ _ ih₁ ih₂
  { apply or.inr,
    -- Apply the inductive hypothesis on e₁
    cases or.symm (ih₁ empty) with e₁_steps e₁_iv,

    -- If the LHS steps, apply CONTEXT
    cases e₁_steps with e₁',
    existsi term.app e₁' e₂,
    let E := E.app_left E.hole e₂,
    rw [show term.app e₁  e₂ = E e₁,  from rfl,
        show term.app e₁' e₂ = E e₁', from rfl],
    apply step.context, assumption,

    -- Apply the inductive hypothesis on e₂
    cases or.symm (ih₂ empty) with e₂_steps,

    -- If the RHS steps, apply CONTEXT
    cases e₂_steps with e₂',
    existsi term.app e₁ e₂',
    let E := E.app_right ⟨e₁, e₁_iv⟩ E.hole,
    rw [show term.app e₁ e₂  = E e₂,  from rfl,
        show term.app e₁ e₂' = E e₂', from rfl],
    apply step.context, assumption,

    -- If both are values, then it β-reduces
    cases e₁_iv with x e,
    cases subst e e₂ x with e',
    existsi e',
    apply step.beta, repeat { assumption },

    -- Discard superfluous goals
    cases te₁ }
end

lemma well_typed_halts_is_value {e : term} {τ : type} : well_typed e τ → halts e → is_value e :=
λ t, or.resolve_right (progress rfl t)

/-lemma weakening {Γ : ctx} {e : term} {τ : type} {x : var} :
  well_typed_under Γ e τ → x ∉ dom Γ → extend Γ -/

lemma subst_lemma {x : var} {e e' es : term} {τ τ' : type} {Γ : ctx} :
  Γ = extend emptyf x τ' → well_typed_under Γ e τ → well_typed e' τ' → is_subst es e e' x → well_typed es τ :=
begin
  intros g te te' is,
  induction te generalizing es,

  case well_typed_under.unit
  { cases is, apply well_typed_under.unit },

  case well_typed_under.var _ _ _ h
  { rw g at *,
    cases is,
    
    case is_subst.same_var
    { rw extend_same at h,
      injection h with h',
      rw ←h',
      assumption },
    
    case is_subst.diff_var neq
    { rw extend_diff _ _ neq at h,
      contradiction } },
  
  case well_typed_under.app _ _ _ _ _ _ _ ih₁ ih₂
  { cases is,
    
    case is_subst.app
    { let := ih₁ _ _,
      let := ih₂ _ _,
      apply well_typed_under.app,
      repeat { assumption } } },
  
  case well_typed_under.abs _ _ _ _ _ _ ih
  { rw g at *,
    cases is,
    case is_subst.abs _ neq nfv
    {
      --let h := ih sorry a_3,
      --apply well_typed_under.abs,
      --assumption
      admit
    } }
end

lemma has_unique_type {Γ : ctx} {e : term} {τ τ' : type} :
  well_typed_under Γ e τ → well_typed_under Γ e τ' → τ = τ' :=
begin
  intros t t',
  /-induction t generalizing τ',
  
  cases t',
  refl,

  cases t',
  injection eq.trans a.symm a_1,

  
  let := ih_1 a,-/
  --induction e generalizing Γ τ τ',
  --cases t, cases t',
  --injection eq.trans a_1.symm a_2,

  --cases t, cases t',
  --let := ih_1 a_3 a_3,
  admit
end

lemma E_lemma {E : E} {e e' : term} {τ τ' : type} :
  well_typed (E e) τ → well_typed e τ' → well_typed e' τ' → well_typed (E e') τ :=
begin
  intros tEe te te',
  --induction tEe,
  
  induction E generalizing τ,
  
  
  /-cases tEe,
  let := ih_1 a_2,
  apply well_typed_under.app,
  repeat {assumption},
  
  cases a,
  cases tEe,
  let := ih_1 a_2,
  apply well_typed_under.app,
  repeat {assumption},-/
end

lemma typing_hole {E : E} {e : term} {τ : type} :
  well_typed (E e) τ → ∃ τ', well_typed e τ' :=
begin
  intro t,
  induction E generalizing τ,

  case E.hole
  { existsi τ, assumption },

  case E.app_left _ _ ih
  { cases t,
    case well_typed_under.app _ h
    { exact ih h } },

  case E.app_right v _ ih
  { cases v, cases t,
    case well_typed_under.app _ _ h
    { exact ih h } }
end

lemma preservation {e e' : term} {τ : type} :
  well_typed e τ → (e ⇝ e') → well_typed e' τ :=
begin
  intros t s,
  induction s generalizing τ,
  
  case step.beta
  { cases t,
    cases a_2,
    apply subst_lemma rfl,
    repeat { assumption } },
  
  case step.context _ _ _ _ ih
  { cases typing_hole t with _ t',
    let := ih t',
    apply E_lemma,
    repeat { assumption } },
end

theorem soundness {e e' : term} {τ : type} :
  well_typed e τ → (e ⇝* e') → halts e' → is_value e' ∧ well_typed e' τ :=
begin
  intros t s h,
  induction s,

  case rtc.refl
  { apply and.intro,
    apply well_typed_halts_is_value,
    repeat { assumption } },
  
  -- Ironically, the inductive step is easier...
  case rtc.trans _ _ _ s _ ih
  { exact ih (preservation t s) h }
end

instance {e : term} : decidable (∃ Γ τ, well_typed_under Γ e τ) :=
begin
  induction e,

  case term.unit {
    right, existsi [emptyf, type.unit],
    apply well_typed_under.unit
  },

  case term.var x {
    right, existsi [extend emptyf x type.unit, type.unit],
    apply well_typed_under.var,
    unfold extend, simp
  },

  case term.app e₁ e₂ ih₁ ih₂ {
    cases ih₁ with n₁ y₁,

    left, intro h,
    cases h with Γ h, cases h with τ te₁,
    cases te₁,
    exact n₁ ⟨Γ, type.func τ_1 τ, a⟩,

    cases ih₂ with n₂ y₂,

    left, intro h,
    cases h with Γ h, cases h with τ te₂,
    cases te₂,
    exact n₂ ⟨Γ, τ_1, a_1⟩,

    right, cases y₁ with Γ₁ y₁, cases y₂ with Γ₂ y₂,
    cases y₁ with τ₁ te₁, cases y₂ with τ₂ te₂,
    cases τ₁,
    
    --existsi [emptyf, type.func τ₁ τ₂],
    --apply well_typed_under.app,

  }

  /-case term.abs _ _ ih {
    cases ih with n y,

    left, intro h,
    cases h with _ t,
    cases t,
    
  }-/


end