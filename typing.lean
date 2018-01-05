import .core .partial_fun

def ctx := partial_fun var type

inductive has_type_under : ctx → term → type → Prop
| unit {Γ : ctx} :
    has_type_under Γ term.unit type.unit

| var {Γ : ctx} {x : var} {τ : type} :
    Γ x = τ → has_type_under Γ (term.var x) τ

| abs {Γ : ctx} {x : var} {e : term} {τ τ' : type} :
    has_type_under (extend Γ x τ) e τ' → has_type_under Γ (term.abs x e) (type.func τ τ')

| app {Γ : ctx} {e₁ e₂ : term} {τ τ' : type} :
    has_type_under Γ e₁ (type.func τ τ') → has_type_under Γ e₂ τ →
      has_type_under Γ (term.app e₁ e₂) τ'

@[reducible]
def has_type := has_type_under emptyf