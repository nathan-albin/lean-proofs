import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Matroid

-- We're working with a finite ground set
variable {α : Type*} [Fintype α]

-- A probability mass function on the bases of a matroid.
structure BasePMF (M : Matroid α) where

  -- assigns a real number to subsets of the ground set
  toFun : Finset α → ℝ

  -- is non-negative on all subsets
  nonneg' : ∀ B, 0 ≤ toFun B

  -- only bases have positive mass
  support' : ∀ B, toFun B ≠ 0 → M.IsBase B

  -- the total mass sums to 1
  sum_one' : ∑ B, toFun B = 1

-- Allow PMF to act as a function.
instance {M : Matroid α} : CoeFun (BasePMF M) (fun _ => Finset α → ℝ) where
  coe p := p.toFun

-- Helpful theorems.
variable {M : Matroid α} (p : BasePMF M)

@[simp] theorem BasePMF.nonneg (B : Finset α) : 0 ≤ p B :=
  p.nonneg' B

@[simp] theorem BasePMF.support (B : Finset α) :
  p B ≠ 0 → M.IsBase B :=
  p.support' B

@[simp] theorem BasePMF.sum_one : ∑ B, p B = 1 :=
  p.sum_one'

section ExpectedUsage

variable [DecidableEq α]

def ExpectedUsage (e : α) : ℝ :=
  ∑ B, p B * (if e ∈ B then 1 else 0)

theorem sum_expected_usage :
  ∑ e, ExpectedUsage p e = M.eRank.toNat := by
  calc
    ∑ e, ExpectedUsage p e
        = ∑ e, ∑ B, p B * (if e ∈ B then 1 else 0) := by simp [ExpectedUsage]
      _ = ∑ B, p B * (∑ e, if e ∈ B then 1 else 0) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ = ∑ B, p B * (M.eRank.toNat) := by
        apply Finset.sum_congr rfl
        intro B h
        rw [Finset.sum_ite]
        simp only [Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul, mul_one,
          mul_eq_mul_left_iff]
        by_cases hP : p.toFun B = 0
        · simp [hP]
        · have hB : M.IsBase B := p.support B hP
          rw [← Matroid.IsBase.encard_eq_eRank hB]
          left
          simp
      _= M.eRank.toNat := by
        simp_rw [mul_comm]
        rw [← Finset.mul_sum]
        simp [p.sum_one]

end ExpectedUsage

end Matroid
