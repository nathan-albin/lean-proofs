import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

structure ObjectFamily (α : Type*) where
  -- objects live in a ground set
  (E : Set α)
  -- there is a usage function on objects
  (N : Set α → α → ℝ)
  -- we can tell if a set is a member of the family
  (IsObject : Set α → Prop)
  -- every object lives on E
  (subset_ground : ∀ γ, IsObject γ → γ ⊆ E)
  -- the usage function is non-negative
  (nonneg : ∀ γ e, N γ e ≥ 0)

namespace Modulus

variable {α : Type*} [Fintype α] (Γ : ObjectFamily α)

def IsAdmissible (ρ : α → ℝ) : Prop :=
  ∀ γ, Γ.IsObject γ → (∑ e ∈ γ, ρ e ≥ 1)

end Modulus
