import AverageSensitivity.MADMonotone
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The Wallis estimate: `mad n ≤ √(n/(2π))` up to the odd/even correction

R7-FORMALIZATION-PLAN ingredient 4 (paper §6, eqs. 18–19). The chain:

* `wallis_mul_central_sq`: the normalized central binomial coefficient and the
  Wallis product cancel exactly — `(2k+1) · W k · (central k)² = 1`.  Proved by
  a one-line induction on `W_succ` + `sq_central_succ_mul`; no factorials.
* **eq. 18** — `central k² ≤ 4/(π(4k+1))`, i.e. `c_k² ≤ 1/(π(k+1/4))`.  The
  paper's engine is the *increasing* sequence `(k+1/4)·c_k²` — it rises to the
  limit `1/π`, so every term sits below `1/π`.  Here: `centralSqScaled` is
  monotone (`(4k+5)(2k+1)² − (4k+1)(2k+2)² = 1 > 0` times `c_k²`) and its limit
  is `4/π` from `tendsto_W_nhds_pi_div_two`, so `Monotone.ge_of_tendsto` gives
  the bound.  Note `le_W` alone is *not* strong enough (it yields
  `c_k² ≤ 2(2k+2)/(π(2k+1)²)`, missing eq. 18 by exactly `k ≤ 0`); the limit of
  the increasing sequence is what sharpens the squeeze.
* **eq. 19** — `2π·(mad n)²/n ≤ 2n/(2n+1)` for even `n` and `≤ 2n/(2n−1)` for
  odd `n`, i.e. `mad n ≤ √((n/2π)·(2n/(2n±1)))`.  The bare `mad n ≤ √(n/(2π))`
  holds for even `n`; the odd subsequence carries the `(2n−1)` correction.
* the uniform block corollary `2π·(mad n)²·(n+d)² ≤ n·(n+2d)²` — the squared
  form of `√(2π)·b_n·(n+d)/(√n·(n+2d)) ≤ 1` (their last three displays).  For
  odd `n` this needs `d ≥ 1` (the odd-n absorption; at `d = 0` the odd value
  `mad 1 = 1/2` beats `√(1/2π)`).
* `cert_8_div_sqrt_two_pi_lt`: the rational certificate `8/√(2π) < 399/125`.
  It needs only `π > 3.14069`; Mathlib's `Real.pi_gt_d4` (`3.1415 < π`) already
  suffices, so the arctan(1/2)+arctan(1/3) route is unnecessary.
-/

open Filter
open scoped BigOperators Topology

namespace AverageSensitivity

/-! ## Positivity of the weights -/

theorem central_nonneg (k : ℕ) : 0 ≤ central k := by
  unfold central
  positivity

theorem central_pos (k : ℕ) : 0 < central k := by
  unfold central
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos k) (by positivity)

/-! ## The Wallis product cancels `central k` -/

/-- `(2k+1) · W k · (central k)² = 1` — the exact bridge between the Wallis
product and the normalized central binomial coefficient. -/
theorem wallis_mul_central_sq (k : ℕ) :
    ((2:ℝ)*k+1) * Real.Wallis.W k * (central k)^2 = 1 := by
  induction k with
  | zero => norm_num [Real.Wallis.W, central, Nat.centralBinom]
  | succ k ih =>
    have h1 : (2*(k:ℝ)+1) ≠ 0 := by positivity
    have h2 : (2*(k:ℝ)+2) ≠ 0 := by positivity
    have h3 : (2*(k:ℝ)+3) ≠ 0 := by positivity
    have hc : (central (k+1))^2 = (2*(k:ℝ)+1)^2 * (central k)^2 / (2*(k:ℝ)+2)^2 := by
      rw [eq_div_iff (by positivity : (2*(k:ℝ)+2)^2 ≠ 0), mul_comm]
      exact sq_central_succ_mul k
    push_cast
    rw [show (2:ℝ)*(k+1)+1 = 2*(k:ℝ)+3 by ring, Real.Wallis.W_succ, hc]
    have key : (2*(k:ℝ)+3) * (Real.Wallis.W k * ((2*(k:ℝ)+2)/(2*(k:ℝ)+1) *
        ((2*(k:ℝ)+2)/(2*(k:ℝ)+3)))) * ((2*(k:ℝ)+1)^2 * (central k)^2 / (2*(k:ℝ)+2)^2)
        = (2*(k:ℝ)+1) * Real.Wallis.W k * (central k)^2 := by
      field_simp [h1, h2, h3]
    rw [key, ih]

/-- Closed form: `central k² = 1/((2k+1)·W k)`. -/
theorem central_sq_eq (k : ℕ) : (central k)^2 = ((2*(k:ℝ)+1) * Real.Wallis.W k)⁻¹ :=
  eq_inv_of_mul_eq_one_right (wallis_mul_central_sq k)

/-! ## The increasing sequence `(k+1/4) · central k²` (paper eq. 18's engine) -/

/-- The scaled central square of the paper's increasing-sequence argument:
`centralSqScaled k = (4k+1) · (central k)²` — its limit is `4/π`. -/
noncomputable def centralSqScaled (k : ℕ) : ℝ := (4*(k:ℝ)+1) * (central k)^2

/-- **The sequence increases**: `(4k+5)·c_{k+1}² ≥ (4k+1)·c_k²`, with gap
exactly `(central k)²/(2k+2)² ≥ 0` since `(4k+5)(2k+1)² − (4k+1)(2k+2)² = 1`. -/
theorem centralSqScaled_succ_le (k : ℕ) : centralSqScaled k ≤ centralSqScaled (k+1) := by
  have hpos : 0 < (2*(k:ℝ)+2)^2 := by positivity
  have hkey : (2*(k:ℝ)+2)^2 * (centralSqScaled (k+1) - centralSqScaled k)
      = (central k)^2 := by
    have hc : (central (k+1))^2 = (2*(k:ℝ)+1)^2 * (central k)^2 / (2*(k:ℝ)+2)^2 := by
      rw [eq_div_iff (by positivity : (2*(k:ℝ)+2)^2 ≠ 0), mul_comm]
      exact sq_central_succ_mul k
    unfold centralSqScaled
    push_cast
    rw [hc]
    field_simp [hpos.ne']
    ring
  nlinarith [hkey, sq_nonneg (central k), hpos]

theorem centralSqScaled_monotone : Monotone centralSqScaled :=
  monotone_nat_of_le_succ centralSqScaled_succ_le

/-- **The limit is `4/π`**: `centralSqScaled k = ((4k+1)/(2k+1))·(W k)⁻¹ → 2·(π/2)⁻¹ = 4/π`. -/
theorem centralSqScaled_tendsto :
    Tendsto (fun k : ℕ => centralSqScaled k) atTop (𝓝 (4/Real.pi)) := by
  have hform : (fun k : ℕ => centralSqScaled k)
      = fun k : ℕ => ((4*(k:ℝ)+1)/(2*(k:ℝ)+1)) * (Real.Wallis.W k)⁻¹ := by
    ext k
    rw [centralSqScaled, central_sq_eq]
    field_simp [(by positivity : (2*(k:ℝ)+1) ≠ 0), (Real.Wallis.W_pos k).ne']
  have hA : Tendsto (fun k : ℕ => ((4*(k:ℝ)+1)/(2*(k:ℝ)+1))) atTop (𝓝 2) := by
    have h : (fun k : ℕ => ((4*(k:ℝ)+1)/(2*(k:ℝ)+1)))
        = fun k : ℕ => 2 - 1/(2*(k:ℝ)+1) := by
      ext k
      field_simp
      ring
    rw [h]
    have h1 : Tendsto (fun k : ℕ => (1:ℝ)/(2*(k:ℝ)+1)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      refine Tendsto.atTop_add ?_ tendsto_const_nhds
      exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < (2:ℝ))
    have h2 : Tendsto (fun k : ℕ => (2:ℝ) - 1/(2*(k:ℝ)+1)) atTop (𝓝 (2 - (0:ℝ))) :=
      tendsto_const_nhds.sub h1
    rw [sub_zero] at h2
    exact h2
  have hB : Tendsto (fun k : ℕ => (Real.Wallis.W k)⁻¹) atTop (𝓝 ((Real.pi/2)⁻¹)) :=
    Real.Wallis.tendsto_W_nhds_pi_div_two.inv₀ Real.pi_div_two_pos.ne'
  have h2 : (2:ℝ) * (Real.pi/2)⁻¹ = 4/Real.pi := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hform, ← h2]
  exact hA.mul hB

/-! ## Paper eq. 18: `central k² ≤ 4/(π(4k+1))` -/

/-- **eq. 18, division-free**: `π·(4k+1)·(central k)² ≤ 4`. -/
theorem central_sq_mul_le (k : ℕ) :
    Real.pi * ((4*(k:ℝ)+1) * (central k)^2) ≤ 4 := by
  have hle := Monotone.ge_of_tendsto centralSqScaled_monotone centralSqScaled_tendsto k
  rw [centralSqScaled] at hle
  have hmul : Real.pi * ((4*(k:ℝ)+1) * (central k)^2) ≤ Real.pi * (4 / Real.pi) :=
    mul_le_mul_of_nonneg_left hle Real.pi_pos.le
  have h4 : Real.pi * (4 / Real.pi) = 4 := by
    field_simp [Real.pi_ne_zero]
  rw [h4] at hmul
  exact hmul

/-- **Paper eq. 18** — the Wallis estimate on the normalized central binomial
coefficient: `(central k)² ≤ 4/(π(4k+1)) = 1/(π(k+1/4))`. -/
theorem central_sq_le (k : ℕ) : (central k)^2 ≤ 4/(Real.pi*(4*(k:ℝ)+1)) := by
  have hpos : 0 < Real.pi * (4*(k:ℝ)+1) := by positivity
  have h := central_sq_mul_le k
  have key : (central k)^2 * (Real.pi * (4*(k:ℝ)+1))
      = Real.pi * ((4*(k:ℝ)+1) * (central k)^2) := by ring
  rw [le_div_iff₀ hpos, key]
  exact h

/-! ## Paper eq. 19: `2π·(mad n)²/n` against `2n/(2n±1)` -/

/-- **eq. 19, even case** (`n = 2k`): `2π·(mad 2k)²/(2k) ≤ 2n/(2n+1) = 4k/(4k+1)`.
True at `k = 0` in Lean's totalized division (`0 ≤ 0`). -/
theorem mad_even_sq_le (k : ℕ) :
    2*Real.pi*(mad (2*k))^2/(2*(k:ℝ)) ≤ 2*(2*(k:ℝ))/(2*(2*(k:ℝ))+1) := by
  by_cases hk : k = 0
  · subst hk
    norm_num [mad_even, mad_zero]
  · have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h18 := central_sq_mul_le k
    have hstep : Real.pi * (k:ℝ) * (central k)^2 ≤ 4*(k:ℝ)/(4*(k:ℝ)+1) := by
      have h41 : 0 < (4*(k:ℝ)+1) := by positivity
      rw [le_div_iff₀ h41]
      have key : Real.pi * (k:ℝ) * (central k)^2 * (4*(k:ℝ)+1)
          = (k:ℝ) * (Real.pi * ((4*(k:ℝ)+1) * (central k)^2)) := by ring
      rw [key]
      exact (mul_le_mul_of_nonneg_left h18 (le_of_lt hk0)).trans
        (le_of_eq (by ring : (k:ℝ) * 4 = 4*(k:ℝ)))
    rw [mad_even]
    have key2 : 2*Real.pi*((k:ℝ)*central k)^2/(2*(k:ℝ)) = Real.pi * (k:ℝ) * (central k)^2 := by
      field_simp [hk0.ne']
    rw [key2]
    have hR : 2*(2*(k:ℝ))/(2*(2*(k:ℝ))+1) = 4*(k:ℝ)/(4*(k:ℝ)+1) := by ring
    rw [hR]
    exact hstep

/-- **eq. 19, odd case** (`n = 2k+1`): `2π·(mad (2k+1))²/(2k+1) ≤ 2n/(2n−1)`. -/
theorem mad_odd_sq_le (k : ℕ) :
    2*Real.pi*(mad (2*k+1))^2/(2*(k:ℝ)+1) ≤ 2*(2*(k:ℝ)+1)/(2*(2*(k:ℝ)+1)-1) := by
  have h18 := central_sq_mul_le k
  have hn0 : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
  have hstep : Real.pi * (2*(k:ℝ)+1) * (central k)^2 / 2
      ≤ 2*(2*(k:ℝ)+1)/(4*(k:ℝ)+1) := by
    have h41 : 0 < (4*(k:ℝ)+1) := by positivity
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), div_mul_eq_mul_div, le_div_iff₀ h41]
    have key : Real.pi * (2*(k:ℝ)+1) * (central k)^2 * (4*(k:ℝ)+1)
        = (2*(k:ℝ)+1) * (Real.pi * ((4*(k:ℝ)+1) * (central k)^2)) := by ring
    rw [key]
    exact (mul_le_mul_of_nonneg_left h18 (le_of_lt hn0)).trans
      (le_of_eq (by ring : (2*(k:ℝ)+1) * 4 = 2*(2*(k:ℝ)+1)*2))
  rw [mad_odd]
  have key2 : 2*Real.pi*(((2*(k:ℝ)+1)*central k/2))^2/(2*(k:ℝ)+1)
      = Real.pi * (2*(k:ℝ)+1) * (central k)^2 / 2 := by
    field_simp [hn0.ne']
  rw [key2]
  have hR : 2*(2*(k:ℝ)+1)/(2*(2*(k:ℝ)+1)-1) = 2*(2*(k:ℝ)+1)/(4*(k:ℝ)+1) := by ring
  rw [hR]
  exact hstep

/-! ## The estimate in `n`-form -/

/-- **eq. 19 for even `n`**: `2π·(mad n)²/n ≤ 2n/(2n+1)`. -/
theorem mad_sq_le_of_even (n : ℕ) (h : Even n) :
    2*Real.pi*(mad n)^2/(n:ℝ) ≤ 2*(n:ℝ)/(2*(n:ℝ)+1) := by
  obtain ⟨k, rfl⟩ := h
  rw [← two_mul]
  push_cast
  exact mad_even_sq_le k

/-- **eq. 19 for odd `n`**: `2π·(mad n)²/n ≤ 2n/(2n−1)`. -/
theorem mad_sq_le_of_odd (n : ℕ) (h : Odd n) :
    2*Real.pi*(mad n)^2/(n:ℝ) ≤ 2*(n:ℝ)/(2*(n:ℝ)-1) := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  exact mad_odd_sq_le k

/-! ## Square-root form: `mad n ≤ √((n/2π)·(2n/(2n±1)))` -/

/-- **Even `n`**: `mad n ≤ √((n/(2π))·(2n/(2n+1)))`. -/
theorem mad_le_sqrt_of_even (n : ℕ) (h : Even n) :
    mad n ≤ Real.sqrt ((n:ℝ)/(2*Real.pi) * (2*(n:ℝ)/(2*(n:ℝ)+1))) := by
  by_cases hn : n = 0
  · subst hn
    norm_num [mad_zero]
  · have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq := mad_sq_le_of_even n h
    have hpos2 : (0:ℝ) < 2*Real.pi := by positivity
    have key : (2*Real.pi*(mad n)^2/(n:ℝ)) * ((n:ℝ)/(2*Real.pi)) = (mad n)^2 := by
      field_simp [Real.pi_ne_zero, hn0.ne']
    have hmul := mul_le_mul_of_nonneg_right hsq (le_of_lt (div_pos hn0 hpos2))
    rw [key] at hmul
    have hX : 2*(n:ℝ)/(2*(n:ℝ)+1) * ((n:ℝ)/(2*Real.pi))
        = (n:ℝ)/(2*Real.pi) * (2*(n:ℝ)/(2*(n:ℝ)+1)) := by ring
    rw [hX] at hmul
    have := Real.sqrt_le_sqrt hmul
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mad_nonneg n)] at this
    exact this

/-- **Odd `n`**: `mad n ≤ √((n/(2π))·(2n/(2n−1)))` — the bare estimate carries
the odd/even correction `2n/(2n−1)`. -/
theorem mad_le_sqrt_of_odd (n : ℕ) (h : Odd n) :
    mad n ≤ Real.sqrt ((n:ℝ)/(2*Real.pi) * (2*(n:ℝ)/(2*(n:ℝ)-1))) := by
  have hn0 : (0:ℝ) < n := by
    obtain ⟨k, rfl⟩ := h
    push_cast
    positivity
  have hsq := mad_sq_le_of_odd n h
  have hpos2 : (0:ℝ) < 2*Real.pi := by positivity
  have key : (2*Real.pi*(mad n)^2/(n:ℝ)) * ((n:ℝ)/(2*Real.pi)) = (mad n)^2 := by
    field_simp [Real.pi_ne_zero, hn0.ne']
  have hmul := mul_le_mul_of_nonneg_right hsq (le_of_lt (div_pos hn0 hpos2))
  rw [key] at hmul
  have hX : 2*(n:ℝ)/(2*(n:ℝ)-1) * ((n:ℝ)/(2*Real.pi))
      = (n:ℝ)/(2*Real.pi) * (2*(n:ℝ)/(2*(n:ℝ)-1)) := by ring
  rw [hX] at hmul
  have := Real.sqrt_le_sqrt hmul
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mad_nonneg n)] at this
  exact this

/-- **Corollary**: for even `n` the correction `2n/(2n+1) ≤ 1` collapses and the
bare Wallis estimate `mad n ≤ √(n/(2π))` holds. -/
theorem mad_le_sqrt_div_two_pi_of_even (n : ℕ) (h : Even n) :
    mad n ≤ Real.sqrt ((n:ℝ)/(2*Real.pi)) := by
  have h1 := mad_le_sqrt_of_even n h
  have h2 : (n:ℝ)/(2*Real.pi) * (2*(n:ℝ)/(2*(n:ℝ)+1)) ≤ (n:ℝ)/(2*Real.pi) := by
    have hpos : 0 ≤ (n:ℝ)/(2*Real.pi) := by positivity
    have hone : (2*(n:ℝ)/(2*(n:ℝ)+1)) ≤ 1 := by
      rw [div_le_one₀ (by positivity)]
      linarith
    exact mul_le_of_le_one_right hpos hone
  exact h1.trans (Real.sqrt_le_sqrt h2)

/-! ## The uniform block corollary: `√(2π)·b_n·(n+d)/(√n·(n+2d)) ≤ 1` (squared) -/

/-- **Uniform block bound, even `n = 2k`** (squared form of
`√(2π)·mad n·(n+d)/(√n·(n+2d)) ≤ 1`): `2π·(mad 2k)²·(2k+d)² ≤ 2k·(2k+2d)²`. -/
theorem wallis_block_sq_of_even (k d : ℕ) :
    2*Real.pi*(mad (2*k))^2 * ((2*(k:ℝ))+d)^2 ≤ (2*(k:ℝ)) * ((2*(k:ℝ))+2*d)^2 := by
  by_cases hk : k = 0
  · subst hk
    norm_num [mad_even, mad_zero]
  · have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h18 := central_sq_mul_le k
    have h41 : 0 < (4*(k:ℝ)+1) := by positivity
    rw [mad_even, ← mul_le_mul_iff_of_pos_right h41]
    -- goal: 2π·(k·c)²·(2k+d)² * (4k+1) ≤ 2k·(2k+2d)² * (4k+1)
    have h1 : 2*Real.pi*((k:ℝ)*central k)^2 * ((2*(k:ℝ))+d)^2 * (4*(k:ℝ)+1)
        = 2*(k:ℝ)^2*((2*(k:ℝ))+d)^2 * (Real.pi * ((4*(k:ℝ)+1) * (central k)^2)) := by
      ring
    rw [h1]
    have h2 : 0 ≤ 2*(k:ℝ)^2*((2*(k:ℝ))+d)^2 := by positivity
    have h3 : 2*(k:ℝ)^2*((2*(k:ℝ))+d)^2 * 4 = 8*(k:ℝ)^2*((2*(k:ℝ))+d)^2 := by ring
    have hle := mul_le_mul_of_nonneg_left h18 h2
    rw [h3] at hle
    have h4 : 8*(k:ℝ)^2*((2*(k:ℝ))+d)^2 ≤ 2*(k:ℝ)*((2*(k:ℝ))+2*d)^2 * (4*(k:ℝ)+1) := by
      have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
      have hk0' : (0:ℝ) ≤ k := le_of_lt hk0
      nlinarith [mul_nonneg hk0' hd0, mul_nonneg (sq_nonneg (k:ℝ)) hd0,
        mul_nonneg hk0' (sq_nonneg (d:ℝ)), sq_nonneg (k:ℝ), sq_nonneg (d:ℝ)]
    exact hle.trans h4

/-- **Uniform block bound, odd `n = 2k+1`** — needs the odd-n absorption
`d ≥ 1`: `2π·(mad (2k+1))²·(2k+1+d)² ≤ (2k+1)·(2k+1+2d)²`. -/
theorem wallis_block_sq_of_odd (k d : ℕ) (hd : 0 < d) :
    2*Real.pi*(mad (2*k+1))^2 * ((2*(k:ℝ)+1)+d)^2
      ≤ (2*(k:ℝ)+1) * ((2*(k:ℝ)+1)+2*d)^2 := by
  have hn0 : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
  have h18 := central_sq_mul_le k
  have h41 : 0 < (4*(k:ℝ)+1) := by positivity
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  rw [mad_odd, ← mul_le_mul_iff_of_pos_right h41]
  -- goal: 2π·(n·c/2)²·(n+d)² * (4k+1) ≤ n·(n+2d)² * (4k+1), n = 2k+1
  have h1 : 2*Real.pi*(((2*(k:ℝ)+1)*central k/2))^2 * ((2*(k:ℝ)+1)+d)^2 * (4*(k:ℝ)+1)
      = ((2*(k:ℝ)+1)^2 * ((2*(k:ℝ)+1)+d)^2 / 2)
        * (Real.pi * ((4*(k:ℝ)+1) * (central k)^2)) := by
    ring
  rw [h1]
  have h2 : 0 ≤ (2*(k:ℝ)+1)^2 * ((2*(k:ℝ)+1)+d)^2 / 2 := by positivity
  have h3 : ((2*(k:ℝ)+1)^2 * ((2*(k:ℝ)+1)+d)^2 / 2) * 4
      = 2*(2*(k:ℝ)+1)^2*((2*(k:ℝ)+1)+d)^2 := by ring
  have hle := mul_le_mul_of_nonneg_left h18 h2
  rw [h3] at hle
  have h4 : 2*(2*(k:ℝ)+1)^2*((2*(k:ℝ)+1)+d)^2
      ≤ (2*(k:ℝ)+1)*((2*(k:ℝ)+1)+2*d)^2 * (4*(k:ℝ)+1) := by
    -- certificate with u = 2k = n-1 ≥ 0, v = d-1 ≥ 0:
    -- (2n-1)(n+2d)² - 2n(n+d)² = (n-1)((4d-1)(n+1) + 6d²-4d) + 2(d-1)(d+1) + 1
    have hdiff : (2*(k:ℝ)+1)*((2*(k:ℝ)+1)+2*d)^2 * (4*(k:ℝ)+1)
        - 2*(2*(k:ℝ)+1)^2*((2*(k:ℝ)+1)+d)^2
        = (2*(k:ℝ)+1) * (1 + 8*(2*(k:ℝ)) + 4*((d:ℝ)-1) + 16*(2*(k:ℝ))*((d:ℝ)-1)
            + 3*(2*(k:ℝ))^2 + 2*((d:ℝ)-1)^2 + 4*(2*(k:ℝ))^2*((d:ℝ)-1)
            + 6*(2*(k:ℝ))*((d:ℝ)-1)^2) := by ring
    have hu : (0:ℝ) ≤ 2*(k:ℝ) := by positivity
    have hv : (0:ℝ) ≤ (d:ℝ)-1 := by linarith
    have hbr : (0:ℝ) ≤ (1 + 8*(2*(k:ℝ)) + 4*((d:ℝ)-1) + 16*(2*(k:ℝ))*((d:ℝ)-1)
        + 3*(2*(k:ℝ))^2 + 2*((d:ℝ)-1)^2 + 4*(2*(k:ℝ))^2*((d:ℝ)-1)
        + 6*(2*(k:ℝ))*((d:ℝ)-1)^2) := by
      nlinarith [mul_nonneg hu hv, sq_nonneg (2*(k:ℝ)), sq_nonneg ((d:ℝ)-1),
        mul_nonneg (sq_nonneg (2*(k:ℝ))) hv, mul_nonneg hu (sq_nonneg ((d:ℝ)-1))]
    have hm : (0:ℝ) ≤ 2*(k:ℝ)+1 := le_of_lt hn0
    have hnonneg : (0:ℝ) ≤ (2*(k:ℝ)+1)*((2*(k:ℝ)+1)+2*d)^2 * (4*(k:ℝ)+1)
        - 2*(2*(k:ℝ)+1)^2*((2*(k:ℝ)+1)+d)^2 := by
      rw [hdiff]
      exact mul_nonneg hm hbr
    linarith
  exact hle.trans h4

/-! ## The rational certificate: `8/√(2π) < 399/125` -/

/-- **Rational certificate** `8/√(2π) < 399/125 = 3.192` (the paper's witness).
Squaring turns it into `π > 500000/159201 ≈ 3.14068`, and Mathlib's
`Real.pi_gt_d4` (`3.1415 < π`) already covers that — the arctan series route is
not needed. -/
theorem cert_8_div_sqrt_two_pi_lt : (8:ℝ)/Real.sqrt (2*Real.pi) < 399/125 := by
  have h2pi : 0 < 2*Real.pi := by positivity
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr h2pi
  have hR : (0:ℝ) < 399/125 := by norm_num
  have hbase : (0:ℝ) ≤ 399/125 * Real.sqrt (2*Real.pi) := le_of_lt (mul_pos hR hs)
  rw [div_lt_iff₀ hs, ← sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 8) hbase, mul_pow,
    Real.sq_sqrt h2pi.le]
  norm_num only [pow_two]
  -- goal: 64 < 159201/15625 * (2π);  it suffices that π > 3.1415
  have hpi : (3.1415:ℝ) < Real.pi := Real.pi_gt_d4
  have h64 : (64:ℝ) < 159201/15625 * 2 * 3.1415 := by norm_num
  have hconst : (0:ℝ) < 159201/15625 * 2 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hpi.le hconst.le
  linarith

end AverageSensitivity
