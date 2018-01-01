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

lemma subst_lemma {x : var} {e e' es : term} {τ τ' : type} :
  well_typed_under (extend emptyf x τ') e τ → well_typed e' τ' → is_subst es e e' x → well_typed es τ :=
begin
  intros te te' is,
  induction is,

  -- Trivial, since e is already well-typed
  case is_subst.same_var
  { cases te, simp at a,
    injection a with h,
    rw ←h, assumption },
  
  -- Impossible, the context doesn't have y
  case is_subst.diff_var x _ _ h
  { cases te,
    rw [←extend_eta, extend_diff emptyf τ' h] at a,
    contradiction },
  
  -- WTF
  case is_subst.app _ _ _ _ _ x
  { cases te,
    rw ←extend_eta at a_3 a_2,
    simp at a_3 a_2,
    --let := ih_2 a_3,
    admit,
   },
  
  case is_subst.abs 
  {
      cases te,
      rw ←extend_eta at a_3,
      simp at a_3 a_2,
      admit
  }
end

lemma E_lemma {E : E} {e e' : term} {τ τ' : type} :
  well_typed_under emptyf (E e) τ → well_typed_under emptyf e τ' → well_typed_under emptyf e' τ' →
  well_typed (E e') τ :=
begin
  intros tEe te te',
  --induction E,
  --simp [show E.hole e = e, from rfl,show E.hole e' = e', from rfl] at *,
  admit
end

lemma typing_hole {E : E} {e : term} {τ : type} :
  well_typed (E e) τ → ∃ τ', well_typed e τ' :=
begin
  intro t,
  induction E generalizing τ,

  case E.hole
  { existsi τ, assumption },

  case E.app_left _ _ ih
  { cases t, exact ih a_2 },

  case E.app_right v _ ih
  { cases v, cases t, exact ih a_2 }
end

lemma preservation {e e' : term} {τ : type} :
  well_typed e τ → (e ⇝ e') → well_typed e' τ :=
begin
  intros t s,
  induction s generalizing τ,
  
  case step.beta
  { cases t, cases a_2,
    apply subst_lemma,
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
