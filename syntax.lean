def var := ℕ

-- STLC has unit and arrow types
@[derive decidable_eq]
inductive type
| unit : type
| func : type → type → type

-- The AST of terms in STLC
inductive term
| var  : var  → term
| abs  : var → type → term → term
| app  : term → term → term
| unit : term

-- Abstractions and () are values
inductive is_value : set term
| abs (x : var) (τ : type) (e : term) : is_value (term.abs x τ e)
| unit                     : is_value term.unit

def value := subtype is_value

-- Evaluation contexts
inductive E
| hole      : E
| app_left  : E → term → E
| app_right : value → E → E

open E term

def apply : E → term → term
| hole                 t := t
| (app_left  E      e) t := app (apply E t) e
| (app_right ⟨v, _⟩ E) t := app v (apply E t)

instance : has_coe_to_fun E :=
⟨λ _, term → term, apply⟩
