import .typing
import .semantics

def subst (e v : term) (x : var) : {e' // is_subst e' e v x} := sorry

-- Hack: need to state Γ = ∅ since it will refuse to do induction directly on ∣- e : τ
lemma progress {e : term} {τ : type} {Γ : ctx} :
  Γ = emptyf → well_typed_under Γ e τ → is_value e ∨ ∃ e', step e e' :=
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
  case well_typed_under.app _ _ e₁ _ e₂ te₁ _ ih₁ ih₂
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
    cases or.symm (ih₂ empty) with e₂_steps e₂_iv,

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

lemma preservation {e e' : term} {τ : type} :
  well_typed_under emptyf e τ → step e e' → well_typed_under emptyf e' τ :=
begin
  intros t s,
  induction s with e e' E s ih,
    admit,
    admit
end
