def var := ℕ

-- The AST of terms in STLC
inductive term
| var  : var  → term
| abs  : var  → term → term
| app  : term → term → term
| unit : term

-- Abstractions and () are values
inductive is_value : set term
| abs (x : var) (e : term) : is_value (term.abs x e)
| unit                     : is_value term.unit

def value := subtype is_value

-- STLC has unit and arrow types
inductive type
| unit : type
| func : type → type → type

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
