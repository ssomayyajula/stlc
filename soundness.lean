import .typing .semantics

lemma progress {e : term} {τ : type} : has_type e τ → is_value e ∨ ∃ e', e ⇝ e' :=
begin
  unfold has_type,
  generalize g : @emptyf var type = Γ,
  intro h,
  induction h,
  
  -- Impossible, variables cannot be typed in ∅
  case has_type_under.var _ _ _ h
  { rw ←g at h, contradiction },
  
  -- Unit and abstractions are trivially values
  case has_type_under.unit
  { apply or.inl, apply is_value.unit },
  case has_type_under.abs
  { apply or.inl, apply is_value.abs },

  -- Applications always evaluate
  case has_type_under.app _ e₁ e₂ _ _ te₁ _ ih₁ ih₂
  { apply or.inr,
    -- Apply the inductive hypothesis on e₁
    cases (ih₁ g).symm with e₁_steps e₁_iv,

    -- If the LHS steps, apply CONTEXT
    cases e₁_steps with e₁',
    existsi term.app e₁' e₂,
    let E := E.app_left E.hole e₂,
    rw [show term.app e₁  e₂ = E e₁,  from rfl,
        show term.app e₁' e₂ = E e₁', from rfl],
    apply step.context, assumption,

    -- Apply the inductive hypothesis on e₂
    cases (ih₂ g).symm with e₂_steps,

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

lemma has_type_halts_is_value {e : term} {τ : type} : has_type e τ → halts e → is_value e :=
or.resolve_right ∘ progress

lemma ctx_invar {e : term} {τ : type} {Γ : ctx} :
  has_type e τ → ∀ Γ, has_type_under Γ e τ := sorry

-- See technical note in Programming Languages Foundations
-- for why we induct on e as opposed to x:τ' |- e:τ
lemma subst_lemma {x : var} {e e' es : term} {τ τ' : type} {Γ : ctx} :
  has_type_under (extend Γ x τ') e τ → has_type e' τ' → is_subst es e e' x → has_type_under Γ es τ :=
begin
  intros te te' is,

  induction e generalizing Γ τ es,

  case term.unit
  { cases te, cases is,
    apply has_type_under.unit },

  case term.var
  { cases te,

    case has_type_under.var h
    { cases is,

      case is_subst.same_var
      { rw extend_same at h,
        injection h with h,
        rw ←h, apply ctx_invar, assumption, assumption },
      
      case is_subst.diff_var neq
      { rw extend_diff Γ τ' neq at h,
        apply has_type_under.var, assumption } } },

  case term.abs y _ ih
  { cases te, cases is,

    apply has_type_under.abs,
    apply ih,
    rw extend_comm _ _ _ a_2,
    repeat { assumption } },

  case term.app
  { cases te, cases is,
    let := ih_1 a_2 a_4,
    let := ih_2 a_3 a_5,
    apply has_type_under.app,
    repeat {assumption} }
end

lemma uniqueness {e : term} {τ τ' : type} :
  has_type e τ → has_type e τ' → τ = τ' := sorry

lemma E_lemma {E : E} {e e' : term} {τ τ' : type} :
  has_type (E e) τ → has_type e τ' → has_type e' τ' → has_type (E e') τ :=
begin
  intros tEe te te',
  
  induction E generalizing τ,
  
  rw uniqueness tEe te,
  assumption,

  cases tEe,
  let := ih_1 a_2,
  apply has_type_under.app,
  repeat {assumption},
  
  cases a,
  cases tEe,
  let := ih_1 a_2,
  apply has_type_under.app,
  repeat {assumption},
end

lemma typing_hole {E : E} {e : term} {τ : type} :
  has_type (E e) τ → ∃ τ', has_type e τ' :=
begin
  intro t,
  induction E generalizing τ,

  case E.hole
  { existsi τ, assumption },

  case E.app_left _ _ ih
  { cases t,
    case has_type_under.app _ h
    { exact ih h } },

  case E.app_right v _ ih
  { cases v, cases t,
    case has_type_under.app _ _ h
    { exact ih h } }
end

lemma preservation {e e' : term} {τ : type} :
  has_type e τ → (e ⇝ e') → has_type e' τ :=
begin
  intros t s,
  induction s generalizing τ,
  
  case step.beta
  { cases t,
    case has_type_under.app _ t'
    { cases t',
      apply subst_lemma,
      repeat { assumption } } },
  
  case step.context _ _ _ _ ih
  { cases typing_hole t with _ t',
    let := ih t',
    apply E_lemma,
    repeat { assumption } },
end

theorem soundness {e e' : term} {τ : type} :
  has_type e τ → (e ⇝* e') → halts e' → is_value e' ∧ has_type e' τ :=
begin
  intros t s h,
  induction s,

  case rtc.refl
  { apply and.intro,
    apply has_type_halts_is_value,
    repeat { assumption } },
  
  case rtc.trans _ _ _ s _ ih
  { exact ih (preservation t s) h }
end
