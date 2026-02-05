import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Matroid

-- establish the scope, we're working with a finite matroid
variable {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)

/-
  The bases of a matroid are constructed by filtering the powerset
  of the ground set.
-/
noncomputable def bases (M : Matroid α) : Finset (Finset α) :=
by
  classical
  exact (Finset.powerset (Finset.univ : Finset α)).filter
    (fun B => M.IsBase (B : Set α))

#check bases M

/-
  A pmf on the bases of M is a function that assigns a non-negative real
  number to each basis of M, such that the sum of these numbers over all
  bases is 1. We can think of this as a probability distribution over the
  bases of M.
-/
structure PmfOnBases {α : Type*} [Fintype α] (M : Matroid α) where
  toFun : Finset α → ℝ
  nonneg : ∀ B, 0 ≤ toFun B
  sum_one : (∑ B ∈ (bases M), toFun B) = 1

def usage (B : Finset α) (e : α) : ℕ :=
  if e ∈ B then 1 else 0

noncomputable def expectedUsage (p : PmfOnBases M) (e : α) : ℝ :=
  ∑ B ∈ (bases M), p.toFun B * (usage B e)

theorem sum_usage_eq_rank (B : Finset α) (h : B ∈ (bases M)) :
  ∑ e, usage B e = M.eRank.toNat := by
  have hb : ∑ e, usage B e = B.card := by
    unfold usage
    rw [Finset.card_eq_sum_ones]
    rw [← Finset.sum_filter]
    simp
  rw [hb]
  #check Finset.mem_filter.mp h
  rw [← Matroid.IsBase.encard_eq_eRank h]



theorem sum_expectedUsage (p : PmfOnBases M) :
  ∑ e, expectedUsage M p e = M.eRank.toNat  := by
  calc
    ∑ e, expectedUsage M p e
        = ∑ e, ∑ B ∈ (bases M), p.toFun B * (usage B e) := by simp [expectedUsage]
      _ = ∑ B ∈ (bases M), p.toFun B * (∑ e, usage B e) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ = ∑ B ∈ (bases M), p.toFun B * (M.eRank.toNat) := by
        apply Finset.sum_congr rfl
        intro b h
        rw [sum_usage_eq_rank]
        grind
      _= M.eRank.toNat := by
        simp_rw [mul_comm]
        rw [← Finset.mul_sum]
        simp [p.sum_one]

#check M.E

end Matroid
