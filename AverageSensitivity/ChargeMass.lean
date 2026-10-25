import Mathlib.Tactic

/-!
# The charge-mass bound: `p ≤ C/(C+1)`

The charged coupling (`RefinedCoupling.finite_coupling_refined_charge`)
charges the `a^2` slack only to indices whose forward step exceeds `2a/3`.
For the d=1 block instantiation (integral steps bounded by 1) those are
exactly the `V - U = 1` indices, and equal marginals pin the forward mass
to the backward mass, which the range bound caps at `C` per unit weight.
-/

open scoped BigOperators
namespace AverageSensitivity

theorem charge_mass_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (w U V : Ω → ℝ) (C : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (hstep : ∀ i, w i ≠ 0 → V i - U i ≤ 1)
    (hint : ∀ i, ∃ k : ℤ, V i - U i = (k:ℝ))
    (hC : (1:ℝ) ≤ C) (hCbound : ∀ i, w i ≠ 0 → |V i - U i| ≤ C) :
    (∑ i, if 2/(3:ℝ) < V i - U i then w i else 0) ≤ C/(C+1) := by
  classical
  have hC0 : (0:ℝ) ≤ C := by linarith
  -- the drift is zero on equal marginals
  have hzero : ∑ i, w i * (V i - U i) = 0 := by
    have h1 : (∑ i, w i * U i) = (∑ i, w i * V i) := hsame (fun t => t)
    have hsplit : ∑ i, w i * (V i - U i) =
        (∑ i, w i * V i) - (∑ i, w i * U i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsplit, h1, sub_self]
  -- on the support: forward steps are exactly 1; quiet steps are exactly 0
  have hfwd_eq : ∀ i, w i ≠ 0 → 2/(3:ℝ) < V i - U i → V i - U i = 1 := by
    intro i hw0 h
    obtain ⟨k, hk⟩ := hint i
    rw [hk] at h
    have hk1 : (1:ℤ) ≤ k := by
      by_contra hcon
      push_neg at hcon
      have hk0 : k ≤ 0 := by omega
      have hle : (k:ℝ) ≤ 0 := Int.cast_nonpos.mpr hk0
      linarith
    have hk2 : k ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hcon
      have := hstep i hw0
      rw [hk] at this
      linarith
    have : (k:ℝ) = 1 := by exact_mod_cast (by omega : k = 1)
    rw [hk, this]
  have hquiet_eq : ∀ i, w i ≠ 0 → ¬(2/(3:ℝ) < V i - U i) → ¬(V i - U i ≤ -1) →
      V i - U i = 0 := by
    intro i hw0 hf hb
    obtain ⟨k, hk⟩ := hint i
    have hk0 : k = 0 := by
      by_contra hcon
      rcases lt_or_ge k 0 with hlt | hge
      · have hc2 : k ≤ -1 := by omega
        have hrm : (k:ℝ) ≤ -1 := by exact_mod_cast hc2
        apply hb
        rw [hk]
        exact hrm
      · have hk1 : (1:ℤ) ≤ k := by omega
        have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
        apply hf
        rw [hk]
        linarith
    rw [hk, hk0]
    norm_num
  -- decompose the drift into the forward, middle, and backward classes
  -- (the three conditions partition ℝ: > 2/3, ≤ -1, or the middle)
  have hdecomp : ∀ i, w i * (V i - U i) =
      (if 2/(3:ℝ) < V i - U i then w i * (V i - U i) else 0) +
      (if V i - U i ≤ -1 then w i * (V i - U i) else 0) +
      (if ¬(2/(3:ℝ) < V i - U i) ∧ ¬(V i - U i ≤ -1) then w i * (V i - U i) else 0) := by
    intro i
    by_cases h1 : 2/(3:ℝ) < V i - U i
    · have hnot2 : ¬(V i - U i ≤ -1) := by intro h2; linarith
      have hnot3 : ¬(¬(2/(3:ℝ) < V i - U i) ∧ ¬(V i - U i ≤ -1)) := fun hc => hc.1 h1
      rw [if_pos h1, if_neg hnot2, if_neg hnot3]
      ring
    · rw [if_neg h1]
      by_cases h2 : V i - U i ≤ -1
      · have hnot3 : ¬(¬(2/(3:ℝ) < V i - U i) ∧ ¬(V i - U i ≤ -1)) := fun hc => hc.2 h2
        rw [if_pos h2, if_neg hnot3]
        ring
      · rw [if_neg h2, if_pos ⟨h1, h2⟩]
        ring
  have hsum_decomp : ∑ i, w i * (V i - U i) =
      (∑ i, if 2/(3:ℝ) < V i - U i then w i * (V i - U i) else 0) +
      (∑ i, if V i - U i ≤ -1 then w i * (V i - U i) else 0) +
      (∑ i, if ¬(2/(3:ℝ) < V i - U i) ∧ ¬(V i - U i ≤ -1) then w i * (V i - U i) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hdecomp i)
  -- the middle class contributes nothing
  have hquiet_sum : (∑ i, if ¬(2/(3:ℝ) < V i - U i) ∧ ¬(V i - U i ≤ -1) then w i * (V i - U i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hcls : ¬(2/(3:ℝ) < V i - U i) ∧ ¬(V i - U i ≤ -1)
    · rw [if_pos hcls]
      by_cases hw0 : w i = 0
      · simp [hw0]
      · rw [hquiet_eq i hw0 hcls.1 hcls.2]
        ring
    · rw [if_neg hcls]
  -- the forward class carries exactly its weight
  have hfwd_sum : (∑ i, if 2/(3:ℝ) < V i - U i then w i * (V i - U i) else 0) =
      (∑ i, if 2/(3:ℝ) < V i - U i then w i else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h1 : 2/(3:ℝ) < V i - U i
    · rw [if_pos h1, if_pos h1]
      by_cases hw0 : w i = 0
      · simp [hw0]
      · rw [hfwd_eq i hw0 h1]
        ring
    · rw [if_neg h1, if_neg h1]
  -- so p equals the backward mass
  have hsplit0 : (∑ i, if 2/(3:ℝ) < V i - U i then w i * (V i - U i) else 0) +
      (∑ i, if V i - U i ≤ -1 then w i * (V i - U i) else 0) = 0 := by
    have h3 := hsum_decomp
    have hq := hquiet_sum
    linarith [h3, hq]
  have h4 : (∑ i, if V i - U i ≤ -1 then w i * (V i - U i) else 0) =
      -((∑ i, if V i - U i ≤ -1 then w i * (U i - V i) else 0)) := by
    have hpt : ∀ i : Ω, (if V i - U i ≤ -1 then w i * (V i - U i) else 0) =
        (-(if V i - U i ≤ -1 then w i * (U i - V i) else 0)) := by
      intro i
      by_cases h : V i - U i ≤ -1
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring
    calc (∑ i, if V i - U i ≤ -1 then w i * (V i - U i) else 0)
        = (∑ i, (-(if V i - U i ≤ -1 then w i * (U i - V i) else 0))) :=
          Finset.sum_congr rfl (fun i _ => hpt i)
      _ = -((∑ i, if V i - U i ≤ -1 then w i * (U i - V i) else 0)) := by
          simp
  have hp_eq : (∑ i, if 2/(3:ℝ) < V i - U i then w i else 0) =
      (∑ i, if V i - U i ≤ -1 then w i * (U i - V i) else 0) := by
    have hf := hfwd_sum
    linarith [hsplit0, h4, hf]
  -- the backward mass is at most C times the backward weight
  have hbwd_le : (∑ i, if V i - U i ≤ -1 then w i * (U i - V i) else 0) ≤
      C*(∑ i, if V i - U i ≤ -1 then w i else 0) := by
    have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
        (if V i - U i ≤ -1 then w i * (U i - V i) else 0) ≤
        C*(if V i - U i ≤ -1 then w i else 0) := by
      intro i _
      by_cases h1 : V i - U i ≤ -1
      · rw [if_pos h1, if_pos h1]
        by_cases hw0 : w i = 0
        · simp [hw0]
        · have := hCbound i hw0
          rw [abs_le] at this
          nlinarith [this, hw i, mul_nonneg (hw i) hC0]
      · rw [if_neg h1, if_neg h1]
        exact mul_nonneg hC0 (by simp)
    calc (∑ i, if V i - U i ≤ -1 then w i * (U i - V i) else 0) ≤
          ∑ i, C*(if V i - U i ≤ -1 then w i else 0) :=
        Finset.sum_le_sum hpt
      _ = C*(∑ i, if V i - U i ≤ -1 then w i else 0) := by
        rw [Finset.mul_sum]
  -- forward and backward weights are disjoint parts of the whole
  have hpq : (∑ i, if 2/(3:ℝ) < V i - U i then w i else 0) +
      (∑ i, if V i - U i ≤ -1 then w i else 0) ≤ 1 := by
    have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
        (if 2/(3:ℝ) < V i - U i then w i else 0) +
        (if V i - U i ≤ -1 then w i else 0) ≤ w i := by
      intro i _
      by_cases h1 : 2/(3:ℝ) < V i - U i
      · rw [if_pos h1]
        have hnot2 : ¬(V i - U i ≤ -1) := by intro h2; linarith
        rw [if_neg hnot2]
        linarith [hw i]
      · rw [if_neg h1]
        by_cases h2 : V i - U i ≤ -1
        · rw [if_pos h2]; linarith [hw i]
        · rw [if_neg h2]; linarith [hw i]
    calc (∑ i, if 2/(3:ℝ) < V i - U i then w i else 0) +
          (∑ i, if V i - U i ≤ -1 then w i else 0)
        = ∑ i, ((if 2/(3:ℝ) < V i - U i then w i else 0) +
            (if V i - U i ≤ -1 then w i else 0)) := Finset.sum_add_distrib.symm
      _ ≤ ∑ i, w i := Finset.sum_le_sum hpt
      _ = 1 := hprob
  -- combine: p ≤ C·q and p + q ≤ 1 give p ≤ C/(C+1)
  have hp : (∑ i, if 2/(3:ℝ) < V i - U i then w i else 0) ≤
      C*(∑ i, if V i - U i ≤ -1 then w i else 0) := by
    rw [hp_eq]
    exact hbwd_le
  have hfinal : (∑ i, if 2/(3:ℝ) < V i - U i then w i else 0)*(1+C) ≤ C := by
    nlinarith [hp, hpq, hC]
  have hpos : (0:ℝ) < 1+C := by linarith
  rw [show C/(C+1) = C/(1+C) from by ring]
  exact (le_div_iff₀ hpos).mpr hfinal

end AverageSensitivity
