import OAI.Combinatorics.GotsmanLinial.ScalarIncrements
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! The finite one-sided refinement from Lagdive--Aglave--Damre,
`An elementary improvement ...`, Lemma 2. The proof here uses a single
pointwise majorant and cancellation of equal-marginal potential sums. -/
open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial

namespace AverageSensitivity

theorem displacement_majorant (m a u v : ℝ) (ha : 0 ≤ a)
    (hstep : v-u ≤ a) :
    (u-v)^2 ≤ 4 * (couplingPotential m u - couplingPotential m v) +
      2*a*(|u-m|+|v-m|) + a^2 := by
  have hsum : 0 ≤ |u-m|+|v-m| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  by_cases huv : u ≤ v
  · have h := (couplingPotential_increment_bounds m huv).2
    have hprod := mul_nonneg (sub_nonneg.mpr hstep) hsum
    have hsq := mul_nonneg (sub_nonneg.mpr hstep) (show 0 ≤ a+(v-u) by linarith)
    nlinarith
  · have hvu : v ≤ u := le_of_not_ge huv
    have h := (couplingPotential_increment_bounds m hvu).1
    have hprod := mul_nonneg ha hsum
    nlinarith [sq_nonneg a]

theorem finite_coupling_refined {Ω : Type*} [Fintype Ω]
    (w U V : Ω → ℝ) (m a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (ha : 0 ≤ a) (hstep : ∀ i, w i ≠ 0 → V i-U i ≤ a) :
    ∑ i, w i*(U i-V i)^2 ≤ 4*a*(∑ i, w i*|U i-m|)+a^2 := by
  have hpoint : ∀ i, w i*(U i-V i)^2 ≤
      w i*(4*(couplingPotential m (U i)-couplingPotential m (V i)) +
        2*a*(|U i-m|+|V i-m|)+a^2) := by
    intro i
    by_cases hi : w i = 0
    · simp only [hi, zero_mul, mul_zero]
      norm_num
    · exact mul_le_mul_of_nonneg_left (displacement_majorant m a _ _ ha (hstep i hi)) (hw i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hp := hsame (couplingPotential m)
  have habs := hsame (fun t => |t-m|)
  have heq : (∑ i, w i*(4*(couplingPotential m (U i)-couplingPotential m (V i)) +
        2*a*(|U i-m|+|V i-m|)+a^2)) =
      4*((∑ i, w i*couplingPotential m (U i))-(∑ i, w i*couplingPotential m (V i))) +
      2*a*((∑ i, w i*|U i-m|)+(∑ i, w i*|V i-m|)) + a^2*(∑ i,w i) := by
    simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    simp only [mul_left_comm, mul_comm, mul_assoc]
  rw [heq, hp, sub_self, mul_zero, zero_add, hprob, mul_one, ← habs] at h
  nlinarith

/-- The good-step majorant: when the forward step is at most `2a/3`, the
uniform `a^2` charge is unnecessary — the `2a(|u-m|+|v-m|)` term already
covers the displacement. (The `a^2` is consumed only by the largest steps;
charging it to every pair is the slack the exported `+2d^2` carries.) -/
theorem displacement_majorant_good (m a u v : ℝ) (ha : 0 ≤ a)
    (hstep : v - u ≤ 2*a/3) :
    (u-v)^2 ≤ 4 * (couplingPotential m u - couplingPotential m v) +
      2*a*(|u-m|+|v-m|) := by
  have hsum : 0 ≤ |u-m|+|v-m| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS : |v-u| ≤ |u-m|+|v-m| := by
    have h1 : |u-v| ≤ |u-m| + |m-v| := by
      have h := abs_add_le (u-m) (m-v)
      rw [show (u-m)+(m-v) = u-v from by ring] at h
      exact h
    rw [abs_sub_comm m v] at h1
    rw [show |u-v| = |v-u| from abs_sub_comm u v] at h1
    exact h1
  by_cases huv : u ≤ v
  · have hδ : (0:ℝ) ≤ v - u := by linarith
    have had : (0:ℝ) ≤ a - (v-u) := by nlinarith [hstep, ha]
    have hle2 : (0:ℝ) ≤ 2*a - 3*(v-u) := by nlinarith [hstep, ha]
    have hS' : (v-u) ≤ |u-m|+|v-m| := by
      rw [abs_of_nonneg hδ] at hS
      exact hS
    have h := (couplingPotential_increment_bounds m huv).2
    have e2 : (0:ℝ) ≤ 4*(couplingPotential m u - couplingPotential m v) +
        2*a*(|u-m|+|v-m|) + 2*(v-u)*(|u-m|+|v-m|) - (u-v)^2 := by
      nlinarith [h, hδ]
    have e4 : (v-u)*(a-(v-u)) ≤ (|u-m|+|v-m|)*(a-(v-u)) :=
      mul_le_mul_of_nonneg_right hS' had
    have e6 : (0:ℝ) ≤ (v-u)*(2*a - 3*(v-u)) := mul_nonneg hδ hle2
    nlinarith [e2, e4, e6, hδ]
  · have hvu : v ≤ u := by linarith
    have h := (couplingPotential_increment_bounds m hvu).1
    nlinarith [h, hsum, mul_nonneg ha hsum]

/-- The charged finite coupling: the `a^2` slack is charged only to the
indices whose forward step exceeds `2a/3`, instead of uniformly. On equal
marginals the potential and absolute-deviation sums still cancel completely —
only the charged mass `∑ i, (if 2a/3 < V i - U i then w i else 0)` survives. -/
theorem finite_coupling_refined_charge {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (w U V : Ω → ℝ) (m a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (ha : 0 ≤ a)
    (hstep : ∀ i, w i ≠ 0 → V i - U i ≤ a) :
    ∑ i, w i*(U i-V i)^2 ≤
      4*a*(∑ i, w i*|U i-m|) +
      a^2*(∑ i, if 2*a/3 < V i - U i then w i else 0) := by
  classical
  have hpoint : ∀ i, w i*(U i-V i)^2 ≤
      w i*(4*(couplingPotential m (U i)-couplingPotential m (V i)) +
        2*a*(|U i-m|+|V i-m|)) +
      a^2*(if 2*a/3 < V i - U i then w i else 0) := by
    intro i
    by_cases hi : w i = 0
    · simp only [hi, zero_mul]
      split_ifs <;> norm_num
    · by_cases hbad : 2*a/3 < V i - U i
      · have hstp := hstep i hi
        have h := displacement_majorant m a (U i) (V i) ha hstp
        have h2 := mul_le_mul_of_nonneg_left h (hw i)
        have hring : w i*(4*(couplingPotential m (U i)-couplingPotential m (V i)) +
            2*a*(|U i-m|+|V i-m|) + a^2) =
            w i*(4*(couplingPotential m (U i)-couplingPotential m (V i)) +
            2*a*(|U i-m|+|V i-m|)) + a^2*(w i) := by ring
        rw [hring] at h2
        rw [if_pos hbad]
        exact h2
      · have hgd : V i - U i ≤ 2*a/3 := le_of_not_gt hbad
        have h := displacement_majorant_good m a (U i) (V i) ha hgd
        rw [if_neg hbad, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left h (hw i)
  have hsummed := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_add_distrib] at hsummed
  have hp := hsame (couplingPotential m)
  have habs := hsame (fun t => |t-m|)
  have heq : (∑ i, w i*(4*(couplingPotential m (U i)-couplingPotential m (V i)) +
        2*a*(|U i-m|+|V i-m|))) =
      4*((∑ i, w i*couplingPotential m (U i))-(∑ i, w i*couplingPotential m (V i))) +
      2*a*((∑ i, w i*|U i-m|)+(∑ i, w i*|V i-m|)) := by
    simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    simp only [mul_left_comm, mul_comm, mul_assoc]
  rw [heq, hp, sub_self, mul_zero, zero_add, ← Finset.mul_sum] at hsummed
  have hmid : 2*a*(∑ i, w i*|U i-m| + ∑ i, w i*|V i-m|) +
      a^2*(∑ i, if 2*a/3 < V i - U i then w i else 0) ≤
      4*a*(∑ i, w i*|U i-m|) +
      a^2*(∑ i, if 2*a/3 < V i - U i then w i else 0) := by
    rw [habs]
    linarith
  exact hsummed.trans hmid

end AverageSensitivity
