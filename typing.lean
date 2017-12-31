import .core
import .partial_fun

def ctx := partial_fun var type

inductive well_typed_under : ctx → term → type → Prop
| unit {Γ : ctx} :
    well_typed_under Γ term.unit type.unit

| var {Γ : ctx} (x : var) (τ : type) :
    Γ x = τ → well_typed_under Γ (term.var x) τ

| abs {Γ : ctx} (x : var) (τ : type) (e : term) (τ' : type) :
    well_typed_under (extend Γ x τ) e τ' → well_typed_under Γ (term.abs x e) (type.func τ τ')

| app {Γ : ctx} (τ : type) (e₁ : term) (τ' : type) (e₂ : term) :
    well_typed_under Γ e₁ (type.func τ τ') → well_typed_under Γ e₂ τ →
      well_typed_under Γ (term.app e₁ e₂) τ'

