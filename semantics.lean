import .core

def fv : term → set var
| (term.var x)     := {x}
| (term.app e₁ e₂) := fv e₁ ∪ fv e₂
| (term.abs x e)   := fv e \ {x}
| term.unit        := ∅

-- e' = e{v/x}
inductive is_subst : term → term → term → var → Prop
-- e = x{e/x}
| same_var (x : var) (e : term) : is_subst e (term.var x) e x
-- y = y{e/x}, y ≠ x
| diff_var {x y : var} (e : term) : y ≠ x → is_subst (term.var y) (term.var y) e x
-- e₁{e/x}e₂{e/x} = (e₁ e₂){e/x}
| app {e₁ e₂ e e₁' e₂' : term} {x : var} :
    is_subst e₁' e₁ e x → is_subst e₂' e₂ e x → is_subst (term.app e₁' e₂') (term.app e₁ e₂) e x
-- λ y, e₁{e₂/x} = (λ y, e₁){e₂/x}, y ≠ x, y ∉ fv e₂
| abs {x y : var} {e₁ e₂ e₁' : term} :
    y ≠ x → y ∉ fv e₂ → is_subst e₁' e₁ e₂ x → is_subst (term.abs y e₁') (term.abs y e₁) e₂ x

def subst (e v : term) (x : var) : {e' // is_subst e' e v x} := sorry

inductive step : term → term → Prop
| context {e e' : term} (E : E) :
    step e e' → step (E e) (E e')
| beta {x : var} {e v e' : term}  :
    is_value v → is_subst e' e v x → step (term.app (term.abs x e) v) e'

notation e `⇝` e' := step e e'

-- reflexive transitive closure
inductive rtc {α} (r : α → α → Prop) : α → α → Prop
| refl  : ∀ {a}, rtc a a
| trans : ∀ {a b c}, r a b → rtc b c → rtc a c

def many_steps := rtc step
notation e `⇝*` e' := many_steps e e'

def halts e := ¬∃ e', step e e'
