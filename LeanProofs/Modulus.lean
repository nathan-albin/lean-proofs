import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

-- working with finite gound sets for now
variable {α : Type*} [Fintype α]

structure ObjectFamily where
  -- objects live in a ground set
  (E : Finset α)
  -- there is a usage function on objects
  (N : Finset α → α → ℝ)
  -- we can tell if a set is a member of the family
  (IsObject : Finset α → Prop)
  -- every object lives on E
  (subset_ground : ∀ γ, IsObject γ → γ ⊆ E)
  -- the usage function is non-negative
  (nonneg : ∀ γ e, N γ e ≥ 0)

namespace Modulus

variable {α : Type*} [Fintype α] (Γ : ObjectFamily)

def IsAdmissible (ρ : α → ℝ) : Prop :=
  ∀ γ, Γ.IsObject γ → (∑ e ∈ γ, ρ e ≥ 1)

end Modulus
