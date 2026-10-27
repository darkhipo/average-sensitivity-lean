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

/-- Split a weighted square sum by the sign of the forward step `D = V - U`.
Pure pointwise identity, no hypotheses. -/
theorem drift_sq_split {Ω : Type*} [Fintype Ω] (w U V : Ω → ℝ) :
    ∑ i, w i * (V i - U i)^2 =
      (∑ i, if 0 < V i - U i then w i * (V i - U i)^2 else 0) +
      (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) := by
  classical
  have hpt : ∀ i ∈ (Finset.univ : Finset Ω), w i * (V i - U i)^2 =
      (if 0 < V i - U i then w i * (V i - U i)^2 else 0) +
      (if V i - U i < 0 then w i * (V i - U i)^2 else 0) +
      (if V i - U i = 0 then w i * (V i - U i)^2 else 0) := by
    intro i _
    rcases lt_trichotomy (V i - U i) 0 with h | h | h
    · rw [if_neg (by linarith), if_pos h, if_neg (by linarith)]
      ring
    · rw [if_neg (by linarith), if_neg (by linarith), if_pos h]
      ring
    · rw [if_pos h, if_neg (by linarith), if_neg (by linarith)]
      ring
  have hz : (∑ i, if V i - U i = 0 then w i * (V i - U i)^2 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : V i - U i = 0
    · rw [if_pos h, h]
      ring
    · rw [if_neg h]
  calc ∑ i, w i * (V i - U i)^2 =
      (∑ i, if 0 < V i - U i then w i * (V i - U i)^2 else 0) +
      (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) +
      (∑ i, if V i - U i = 0 then w i * (V i - U i)^2 else 0) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i hi => hpt i hi)
    _ = (∑ i, if 0 < V i - U i then w i * (V i - U i)^2 else 0) +
      (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) := by rw [hz, add_zero]

/-- On equal marginals the positive and negative parts of the drift have the
same weighted mass: `t = E D⁺ = E D⁻`. -/
theorem drift_pos_eq_neg {Ω : Type*} [Fintype Ω] (w U V : Ω → ℝ)
    (hmean : ∑ i, w i * (V i - U i) = 0) :
    (∑ i, w i * max (V i - U i) 0) =
      (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by
  classical
  have hmax : ∀ i ∈ (Finset.univ : Finset Ω),
      w i * (V i - U i) + (if V i - U i < 0 then w i * (U i - V i) else 0) =
      w i * max (V i - U i) 0 := by
    intro i _
    by_cases h : V i - U i < 0
    · rw [if_pos h, max_eq_right (by linarith : V i - U i ≤ 0)]
      ring
    · rw [if_neg h, max_eq_left (by linarith : 0 ≤ V i - U i)]
      ring
  calc (∑ i, w i * max (V i - U i) 0)
      = (∑ i, w i * (V i - U i)) +
          (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i hi => (hmax i hi).symm)
    _ = (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by
        rw [hmean, zero_add]

/-- Three-way split of a weighted sum by the sign of the forward step
`D = V - U`.  Pure pointwise identity, no hypotheses. -/
theorem drift_sum_split_ite {Ω : Type*} [Fintype Ω] (w U V F : Ω → ℝ) :
    ∑ i, w i * F i =
      (∑ i, if 0 < V i - U i then w i * F i else 0) +
      (∑ i, if V i - U i < 0 then w i * F i else 0) +
      (∑ i, if V i - U i = 0 then w i * F i else 0) := by
  classical
  have hpt : ∀ i ∈ (Finset.univ : Finset Ω), w i * F i =
      (if 0 < V i - U i then w i * F i else 0) +
      (if V i - U i < 0 then w i * F i else 0) +
      (if V i - U i = 0 then w i * F i else 0) := by
    intro i _
    rcases lt_trichotomy (V i - U i) 0 with h | h | h
    · rw [if_neg (by linarith), if_pos h, if_neg (by linarith)]
      ring
    · rw [if_neg (by linarith), if_neg (by linarith), if_pos h]
      ring
    · rw [if_pos h, if_neg (by linarith), if_neg (by linarith)]
      ring
  calc ∑ i, w i * F i =
      (∑ i, if 0 < V i - U i then w i * F i else 0) +
      (∑ i, if V i - U i < 0 then w i * F i else 0) +
      (∑ i, if V i - U i = 0 then w i * F i else 0) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i hi => hpt i hi)

/-! ## The compensated coupling (Lagdive–Aglave–Damre, Lemma 2)

The at-term form `E D² + a·t ≤ 4·a·b` under a ONE-sided step `V - U ≤ a`,
via the compensation identity for the potential `couplingPotential m` and
the complement bound `E[A·1_{D>0}] ≤ 2b - t` (`A ≥ |D|` pointwise).  The
center `m` is arbitrary — the paper takes the common mean, but no property
of `m` is used.  See `compensated_coupling_at` below. -/

/-- **Lemma 2 (compensated coupling), at-term form** — Lagdive–Aglave–Damre,
`A compensated coupling bound for the average sensitivity of polynomial
threshold functions`, Lemma 2.  For equal marginals with one-sided step
`V - U ≤ a`, with `b = E|U - m|` (arbitrary center `m`; the paper centers at
the common mean, which the proof never uses) and `t = E D⁺ = E D⁻`:

  `E D² + a·t ≤ 4·a·b`.

The proof: on `D < 0` the LOWER chord bound for `couplingPotential` charges
`D²` to `4·(g U - g V)`; equal marginals give the compensation identity
`E[(g V - g U) 1_{D>0}] = E[(g U - g V) 1_{D<0}]`; on `D > 0` the UPPER
chord bound and the step give `g V - g U ≤ (a/2)·A`, and the complement
`E[A·1_{D>0}] ≤ 2b - t` follows from `A ≥ |D|` pointwise.  This strengthens
the two-sided `compensated_coupling` (CompensatedCoupling.lean) in two ways:
the step hypothesis is one-sided, and the conclusion carries the `+ a·t`
sharpening needed for the finite-range corollary.  Homogeneous in `w`: no
normalization hypothesis. -/
theorem compensated_coupling_at {Ω : Type*} [Fintype Ω]
    (w U V : Ω → ℝ) (m a : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (ha : 0 ≤ a) (hstep : ∀ i, V i - U i ≤ a) :
    (∑ i, w i * (V i - U i)^2) + a * (∑ i, w i * max (V i - U i) 0) ≤
      4 * a * (∑ i, w i * |U i - m|) := by
  classical
  set b : ℝ := ∑ i, w i * |U i - m| with hbdef
  -- pointwise facts
  have hAnneg : ∀ i, 0 ≤ |U i - m| + |V i - m| := fun i =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hAsub : ∀ i, |V i - U i| ≤ |U i - m| + |V i - m| := by
    intro i
    have h1 : |V i - U i| ≤ |V i - m| + |m - U i| := by
      have h := abs_add_le (V i - m) (m - U i)
      have he : V i - m + (m - U i) = V i - U i := by ring
      rw [he] at h
      exact h
    rw [abs_sub_comm m (U i)] at h1
    linarith
  have hchordneg : ∀ i, V i - U i < 0 → (V i - U i)^2 ≤
      4 * (couplingPotential m (U i) - couplingPotential m (V i)) := by
    intro i hneg
    have hvu : V i ≤ U i := le_of_lt (sub_neg.mp hneg)
    have h := couplingPotential_increment_lower m hvu
    have he : (V i - U i)^2 = (U i - V i)^2 := by ring
    rw [he]
    nlinarith [h]
  have hchordpos : ∀ i, 0 < V i - U i →
      couplingPotential m (V i) - couplingPotential m (U i) ≤
        (V i - U i) / 2 * (|U i - m| + |V i - m|) :=
    fun i hpos => couplingPotential_increment_upper m (le_of_lt (sub_pos.mp hpos))
  -- zero-mass sums from equal marginals
  have hmean : ∑ i, w i * (V i - U i) = 0 := by
    have h1 := hsame (fun t => t)
    have hsplit : ∑ i, w i * (V i - U i) =
        (∑ i, w i * V i) - (∑ i, w i * U i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsplit, h1, sub_self]
  have hpot0 : ∑ i, w i *
      (couplingPotential m (V i) - couplingPotential m (U i)) = 0 := by
    have h1 := hsame (couplingPotential m)
    have hsplit : ∑ i, w i *
        (couplingPotential m (V i) - couplingPotential m (U i)) =
        (∑ i, w i * couplingPotential m (V i)) -
        (∑ i, w i * couplingPotential m (U i)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsplit, h1, sub_self]
  -- the compensation identity: E[(gV - gU) 1_{D>0}] = E[(gU - gV) 1_{D<0}]
  have hcomp : (∑ i, if 0 < V i - U i then
        w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) +
      (∑ i, if V i - U i < 0 then
        w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) = 0 := by
    have hgz : (∑ i, if V i - U i = 0 then
        w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : V i - U i = 0
      · have hvu : V i = U i := by linarith
        rw [if_pos h, hvu]
        ring
      · rw [if_neg h]
    have hgs := drift_sum_split_ite w U V
      (fun i => couplingPotential m (V i) - couplingPotential m (U i))
    rw [hgz, add_zero] at hgs
    linarith [hgs, hpot0]
  -- negative side: D² charges to 4·(gU - gV), compensated, then chorded by a/2
  have hneg : (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) ≤
      2 * a * (∑ i, if 0 < V i - U i then
        w i * (|U i - m| + |V i - m|) else 0) := by
    have s1 : (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) ≤
        (∑ i, if V i - U i < 0 then
          w i * (4 * (couplingPotential m (U i) - couplingPotential m (V i))) else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : V i - U i < 0
      · rw [if_pos h, if_pos h]
        exact mul_le_mul_of_nonneg_left (hchordneg i h) (hw i)
      · rw [if_neg h, if_neg h]
    have s2 : (∑ i, if V i - U i < 0 then
          w i * (4 * (couplingPotential m (U i) - couplingPotential m (V i))) else 0) =
        4 * (∑ i, if V i - U i < 0 then
          w i * (couplingPotential m (U i) - couplingPotential m (V i)) else 0) := by
      have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
          (if V i - U i < 0 then
            w i * (4 * (couplingPotential m (U i) - couplingPotential m (V i))) else 0) =
          4 * (if V i - U i < 0 then
            w i * (couplingPotential m (U i) - couplingPotential m (V i)) else 0) := by
        intro i _
        by_cases h : V i - U i < 0
        · rw [if_pos h, if_pos h]
          ring
        · rw [if_neg h, if_neg h]
          ring
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hpt i hi)
    have s3 : (∑ i, if V i - U i < 0 then
          w i * (couplingPotential m (U i) - couplingPotential m (V i)) else 0) =
        -(∑ i, if V i - U i < 0 then
          w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) := by
      have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
          (if V i - U i < 0 then
            w i * (couplingPotential m (U i) - couplingPotential m (V i)) else 0) =
          -((if V i - U i < 0 then
            w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0)) := by
        intro i _
        by_cases h : V i - U i < 0
        · rw [if_pos h, if_pos h]
          ring
        · rw [if_neg h, if_neg h]
          ring
      calc (∑ i, if V i - U i < 0 then
            w i * (couplingPotential m (U i) - couplingPotential m (V i)) else 0)
          = (∑ i, -((if V i - U i < 0 then
            w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0))) :=
            Finset.sum_congr rfl (fun i hi => hpt i hi)
        _ = -(∑ i, if V i - U i < 0 then
            w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) := by
            rw [Finset.sum_neg_distrib]
    have s5 : (∑ i, if 0 < V i - U i then
          w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) ≤
        (a/2) * (∑ i, if 0 < V i - U i then
          w i * (|U i - m| + |V i - m|) else 0) := by
      have h1 : (∑ i, if 0 < V i - U i then
          w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) ≤
          (∑ i, if 0 < V i - U i then
          w i * ((a/2) * (|U i - m| + |V i - m|)) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : 0 < V i - U i
        · rw [if_pos h, if_pos h]
          exact mul_le_mul_of_nonneg_left
            (le_trans (hchordpos i h)
              (mul_le_mul_of_nonneg_right (by linarith [hstep i]) (hAnneg i))) (hw i)
        · rw [if_neg h, if_neg h]
      have h2 : (∑ i, if 0 < V i - U i then
          w i * ((a/2) * (|U i - m| + |V i - m|)) else 0) =
          (a/2) * (∑ i, if 0 < V i - U i then
          w i * (|U i - m| + |V i - m|) else 0) := by
        have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
            (if 0 < V i - U i then
              w i * ((a/2) * (|U i - m| + |V i - m|)) else 0) =
            (a/2) * (if 0 < V i - U i then
              w i * (|U i - m| + |V i - m|) else 0) := by
          intro i _
          by_cases h : 0 < V i - U i
          · rw [if_pos h, if_pos h]
            ring
          · rw [if_neg h, if_neg h]
            ring
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i hi => hpt i hi)
      rw [h2] at h1
      exact h1
    have c3 : -(∑ i, if V i - U i < 0 then
        w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) =
        (∑ i, if 0 < V i - U i then
        w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) := by
      linarith [hcomp]
    calc (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) ≤
          4 * (∑ i, if V i - U i < 0 then
          w i * (couplingPotential m (U i) - couplingPotential m (V i)) else 0) := by
            rw [← s2]; exact s1
      _ = 4 * -(∑ i, if V i - U i < 0 then
          w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) := by rw [s3]
      _ = 4 * (∑ i, if 0 < V i - U i then
          w i * (couplingPotential m (V i) - couplingPotential m (U i)) else 0) := by rw [c3]
      _ ≤ 4 * ((a/2) * (∑ i, if 0 < V i - U i then
          w i * (|U i - m| + |V i - m|) else 0)) :=
            mul_le_mul_of_nonneg_left s5 (by norm_num)
      _ = 2 * a * (∑ i, if 0 < V i - U i then
          w i * (|U i - m| + |V i - m|) else 0) := by ring
  -- positive side: D² ≤ a·D on `0 < D ≤ a`
  have hpos : (∑ i, if 0 < V i - U i then w i * (V i - U i)^2 else 0) ≤
      a * (∑ i, w i * max (V i - U i) 0) := by
    have h1 : (∑ i, if 0 < V i - U i then w i * (V i - U i)^2 else 0) ≤
        (∑ i, if 0 < V i - U i then w i * (a * (V i - U i)) else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : 0 < V i - U i
      · rw [if_pos h, if_pos h]
        have hd : (V i - U i) * (V i - U i) ≤ a * (V i - U i) :=
          mul_le_mul_of_nonneg_right (hstep i) (le_of_lt h)
        nlinarith [hd, hw i]
      · rw [if_neg h, if_neg h]
    have h2 : (∑ i, if 0 < V i - U i then w i * (a * (V i - U i)) else 0) =
        a * (∑ i, if 0 < V i - U i then w i * (V i - U i) else 0) := by
      have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
          (if 0 < V i - U i then w i * (a * (V i - U i)) else 0) =
          a * (if 0 < V i - U i then w i * (V i - U i) else 0) := by
        intro i _
        by_cases h : 0 < V i - U i
        · rw [if_pos h, if_pos h]
          ring
        · rw [if_neg h, if_neg h]
          ring
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hpt i hi)
    have h3 : (∑ i, if 0 < V i - U i then w i * (V i - U i) else 0) =
        (∑ i, w i * max (V i - U i) 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0 < V i - U i
      · rw [if_pos h, max_eq_left (le_of_lt h)]
      · rw [if_neg h, max_eq_right (by linarith : V i - U i ≤ 0)]
        ring
    rw [h2, h3] at h1
    exact h1
  -- complement: E[A·1_{D>0}] ≤ 2b - t (A ≥ |D| pointwise on D < 0)
  have hcompA : (∑ i, if 0 < V i - U i then w i * (|U i - m| + |V i - m|) else 0) +
      (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) ≤ 2 * b := by
    have hAs := drift_sum_split_ite w U V (fun i => |U i - m| + |V i - m|)
    have hIA0nn : 0 ≤ (∑ i, if V i - U i = 0 then
        w i * (|U i - m| + |V i - m|) else 0) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases h : V i - U i = 0
      · rw [if_pos h]
        exact mul_nonneg (hw i) (hAnneg i)
      · rw [if_neg h]
    have hn : (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) ≤
        (∑ i, if V i - U i < 0 then
          w i * (|U i - m| + |V i - m|) else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : V i - U i < 0
      · rw [if_pos h, if_pos h]
        have habs : |U i - V i| ≤ |U i - m| + |V i - m| := by
          have h2 := hAsub i
          rwa [abs_sub_comm (V i) (U i)] at h2
        exact mul_le_mul_of_nonneg_left
          (le_trans (le_abs_self (U i - V i)) habs) (hw i)
      · rw [if_neg h, if_neg h]
    have hb2 : ∑ i, w i * (|U i - m| + |V i - m|) = 2 * b := by
      have habs := hsame (fun t => |t - m|)
      have hsplit : ∑ i, w i * (|U i - m| + |V i - m|) =
          (∑ i, w i * |U i - m|) + (∑ i, w i * |V i - m|) := by
        simp only [mul_add, Finset.sum_add_distrib]
      rw [hsplit, ← habs, ← hbdef]
      ring
    linarith [hAs, hIA0nn, hn, hb2]
  -- assemble
  have hT : (∑ i, w i * max (V i - U i) 0) =
      (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) :=
    drift_pos_eq_neg w U V hmean
  have hX : 2 * a * (∑ i, if 0 < V i - U i then
        w i * (|U i - m| + |V i - m|) else 0) ≤
      4 * a * b - 2 * a * (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by
    have hcompA' : (∑ i, if 0 < V i - U i then w i * (|U i - m| + |V i - m|) else 0) ≤
        2 * b - (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by
      linarith [hcompA]
    calc 2 * a * (∑ i, if 0 < V i - U i then
          w i * (|U i - m| + |V i - m|) else 0) ≤
          2 * a * (2 * b -
            (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0)) :=
              mul_le_mul_of_nonneg_left hcompA' (by linarith)
      _ = 4 * a * b - 2 * a *
            (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by ring
  have hTeq : a * (∑ i, w i * max (V i - U i) 0) =
      a * (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by rw [hT]
  have hK1 := drift_sq_split w U V
  have hfinal : (∑ i, w i * (V i - U i)^2) ≤
      4 * a * b - a * (∑ i, w i * max (V i - U i) 0) := by
    linarith [hK1, hneg, hpos, hX, hTeq]
  linarith [hfinal]

/-- The positive part of the squared drift is at most `a·t` under a one-sided
step `V - U ≤ a`: pointwise `D² ≤ a·D` on `0 < D ≤ a`. -/
theorem pos_sq_sum_le_step {Ω : Type*} [Fintype Ω] (w U V : Ω → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a : ℝ) (hstep : ∀ i, V i - U i ≤ a) :
    (∑ i, if 0 < V i - U i then w i * (V i - U i)^2 else 0) ≤
      a * (∑ i, w i * max (V i - U i) 0) := by
  classical
  have h1 : (∑ i, if 0 < V i - U i then w i * (V i - U i)^2 else 0) ≤
      (∑ i, if 0 < V i - U i then w i * (a * (V i - U i)) else 0) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : 0 < V i - U i
    · rw [if_pos h, if_pos h]
      have hd : (V i - U i) * (V i - U i) ≤ a * (V i - U i) :=
        mul_le_mul_of_nonneg_right (hstep i) (le_of_lt h)
      nlinarith [hd, hw i]
    · rw [if_neg h, if_neg h]
  have h2 : (∑ i, if 0 < V i - U i then w i * (a * (V i - U i)) else 0) =
      a * (∑ i, if 0 < V i - U i then w i * (V i - U i) else 0) := by
    have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
        (if 0 < V i - U i then w i * (a * (V i - U i)) else 0) =
        a * (if 0 < V i - U i then w i * (V i - U i) else 0) := by
      intro i _
      by_cases h : 0 < V i - U i
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => hpt i hi)
  have h3 : (∑ i, if 0 < V i - U i then w i * (V i - U i) else 0) =
      (∑ i, w i * max (V i - U i) 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : 0 < V i - U i
    · rw [if_pos h, max_eq_left (le_of_lt h)]
    · rw [if_neg h, max_eq_right (by linarith : V i - U i ≤ 0)]
      ring
  rw [h2, h3] at h1
  exact h1

/-- The negative part of the squared drift is at most `L·t` under a one-sided
range `U - V ≤ L`: pointwise `D² ≤ L·(-D)` on `D < 0`. -/
theorem neg_sq_sum_le_range {Ω : Type*} [Fintype Ω] (w U V : Ω → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : ℝ) (hrange : ∀ i, U i - V i ≤ L) :
    (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) ≤
      L * (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by
  classical
  have h1 : (∑ i, if V i - U i < 0 then w i * (V i - U i)^2 else 0) ≤
      (∑ i, if V i - U i < 0 then w i * (L * (U i - V i)) else 0) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : V i - U i < 0
    · rw [if_pos h, if_pos h]
      have hd : (U i - V i) * (U i - V i) ≤ L * (U i - V i) :=
        mul_le_mul_of_nonneg_right (hrange i) (by linarith)
      nlinarith [hd, hw i]
    · rw [if_neg h, if_neg h]
  have h2 : (∑ i, if V i - U i < 0 then w i * (L * (U i - V i)) else 0) =
      L * (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by
    have hpt : ∀ i ∈ (Finset.univ : Finset Ω),
        (if V i - U i < 0 then w i * (L * (U i - V i)) else 0) =
        L * (if V i - U i < 0 then w i * (U i - V i) else 0) := by
      intro i _
      by_cases h : V i - U i < 0
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => hpt i hi)
  rw [h2] at h1
  exact h1

/-- **Finite-range corollary (6)** of the compensated coupling — one paragraph
of algebra from `compensated_coupling_at`: with `D⁺ ≤ a` and `D⁻ ≤ L`,
`Q := E D² ≤ (L + a)·t`, and multiplying `Q + a·t ≤ 4ab` by `L + a` and
adding `a·(Q - (L + a)t ≤ 0)` gives `(L + 2a)·Q ≤ 4ab·(L + a)`.  No
integrality, no charge mass; the paper's block instantiation is `L = n`,
`a = d`. -/
theorem compensated_coupling_finite_range {Ω : Type*} [Fintype Ω]
    (w U V : Ω → ℝ) (m a L : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (ha : 0 ≤ a) (hstep : ∀ i, V i - U i ≤ a)
    (hL : 0 < L) (hrange : ∀ i, U i - V i ≤ L) :
    ∑ i, w i * (V i - U i)^2 ≤
      4 * a * (∑ i, w i * |U i - m|) * (L + a) / (L + 2 * a) := by
  classical
  have hmean : ∑ i, w i * (V i - U i) = 0 := by
    have h1 := hsame (fun t => t)
    have hsplit : ∑ i, w i * (V i - U i) =
        (∑ i, w i * V i) - (∑ i, w i * U i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsplit, h1, sub_self]
  have hT : (∑ i, w i * max (V i - U i) 0) =
      (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) :=
    drift_pos_eq_neg w U V hmean
  have hP2 := pos_sq_sum_le_step w U V hw a hstep
  have hN2 := neg_sq_sum_le_range w U V hw L hrange
  have hK1 := drift_sq_split w U V
  have hQ : (∑ i, w i * (V i - U i)^2) ≤ (L + a) * (∑ i, w i * max (V i - U i) 0) := by
    have eL : L * (∑ i, w i * max (V i - U i) 0) =
        L * (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := by rw [hT]
    have eT : (∑ i, w i * max (V i - U i) 0) =
        (∑ i, if V i - U i < 0 then w i * (U i - V i) else 0) := hT
    have hsplit2 : (L + a) * (∑ i, w i * max (V i - U i) 0) =
        L * (∑ i, w i * max (V i - U i) 0) +
        a * (∑ i, w i * max (V i - U i) 0) := by ring
    rw [hsplit2, eL, ← eT]
    linarith [hK1, hP2, hN2]
  have h2 := compensated_coupling_at w U V m a hw hsame ha hstep
  have hL2 : 0 < L + 2 * a := by linarith
  have m1 : (L + a) * ((∑ i, w i * (V i - U i)^2) +
      a * (∑ i, w i * max (V i - U i) 0)) ≤
      (L + a) * (4 * a * (∑ i, w i * |U i - m|)) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have m2 : a * ((∑ i, w i * (V i - U i)^2) -
      (L + a) * (∑ i, w i * max (V i - U i) 0)) ≤ 0 := by
    have hnn : 0 ≤ (L + a) * (∑ i, w i * max (V i - U i) 0) -
        (∑ i, w i * (V i - U i)^2) := sub_nonneg.mpr hQ
    have hEq : a * ((∑ i, w i * (V i - U i)^2) -
        (L + a) * (∑ i, w i * max (V i - U i) 0)) =
        -(a * ((L + a) * (∑ i, w i * max (V i - U i) 0) -
        (∑ i, w i * (V i - U i)^2))) := by ring
    rw [hEq]
    exact neg_nonpos.mpr (mul_nonneg ha hnn)
  have key : (∑ i, w i * (V i - U i)^2) * (L + 2 * a) ≤
      4 * a * (∑ i, w i * |U i - m|) * (L + a) := by
    nlinarith [m1, m2]
  rw [le_div_iff₀ hL2]
  exact key

end AverageSensitivity
