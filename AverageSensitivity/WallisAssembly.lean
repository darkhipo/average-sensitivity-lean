import AverageSensitivity.Multilinearization
import AverageSensitivity.WallisMAD

/-!
# R7 assembly: `AS(f) ≤ (8/√(2π))·d·√n`, closed at the rational `399/125`

The final uniform statement of the R7 campaign.  The four machine-verified
ingredients are combined here and nothing else is touched:

* `block_coupling_finite_range` (BlockRefinement.lean) — the 4-level block
  bound `4·d·mad n·(n+d)/(n+2d)·2ⁿ`, uniform in `d`, from the finite-range
  compensated coupling `compensated_coupling_finite_range` (RefinedCoupling.lean,
  paper eq. (6), instantiated at `a = d`, `L = n`, `m = n/2`);
* the AS(f)-level factor 2 (paper eq. (16)) — the `edge_recovery` /
  `normalized_edge_bound` edge-comparison path of OAI, which doubles the block
  constant to `8·d·mad n·(n+d)/(n+2d)`;
* the Wallis block corollaries `wallis_block_sq_of_even` / `wallis_block_sq_of_odd`
  (WallisMAD.lean, paper eqs. (18)–(19)) — `2π·(mad n)²·(n+d)² ≤ n·(n+2d)²`,
  i.e. `mad n·(n+d)/(n+2d) ≤ √n/√(2π)`;
* the rational certificate `cert_8_div_sqrt_two_pi_lt` (WallisMAD.lean) —
  `8/√(2π) < 399/125`, its squaring needing only `π > 500000/159201`, discharged
  by Mathlib's `Real.pi_gt_d4` (`3.1415 < π`).

Chain: `AS(f) ≤ 8·d·mad n·(n+d)/(n+2d) ≤ (8/√(2π))·d·√n < (399/125)·d·√n`.
The submission-grade deliverable is `AS_bound_399_125`.
-/

open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial

namespace AverageSensitivity

/-! ## AS(f)-level finite-range bound: `AS(f) ≤ 8·d·mad n·(n+d)/(n+2d)`

The grading-level edge comparison (`edge_recovery`, paper eq. (16)) applied to
the uniform 4-level block bound.  `hn : 1 ≤ n` supplies the block range
`L = n > 0`. -/

theorem sensitivity_finite_range_of_grading {n d : ℕ} (hn : 1 ≤ n)
    (f : Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (P : Fin (n + 1) → Matrix (Cube n) (Cube n) ℂ)
    (hP : OrthogonalProjectionFamily P)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (htri : ∀ i : Fin n, BlockTridiagonal P (coordinateSignMatrix i))
    (hvanish : ∀ r s : Fin (n + 1), r.val + s.val < n - d →
      P s * signMatrix (fun x => fullParity x * f x) * P r = 0) :
    averageSensitivity f ≤
      8*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)) := by
  classical
  let h : Cube n → ℝ := fun x => fullParity x * f x
  let H : Matrix (Cube n) (Cube n) ℂ := signMatrix h
  let M : Matrix (Cube n) (Cube n) ℂ := centeredGrading P
  have hh (x : Cube n) : h x = 1 ∨ h x = -1 := parity_twist_cases hf x
  have htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4 := by
    change hsNormSq (centeredGrading P) = _
    rw [hsNormSq_centeredGrading_trace hP]
    simp_rw [htrace]
    simpa only [mul_comm] using sum_choose_centered_sq n
  have hcoordinate (i : Fin n) :
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n := by
    simpa only [M, card_cube, Nat.cast_pow, Nat.cast_ofNat] using
      hsNormSq_centeredGrading_commutator_le_card hP (coordinateSignMatrix i)
        (htri i) (coordinateSignMatrix_unitary i)
  have hdistance :
      (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M := by
    rw [htotal]
    exact distance_energy_le_of_coordinate_commutator_bound M hcoordinate
  have hcap (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
    apply off_diagonal_sq_norm_le_quarter_of_commutator_bound M _ x y hxy
    intro i a b
    exact sq_norm_centeredGrading_commutator_entry_le_one hP (coordinateSignMatrix i)
      (htri i) (coordinateSignMatrix_unitary i) a b
  have hedge : ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * H + H * M) := edge_recovery M h hh htotal hdistance hcap
  have henergy : hsNormSq (M * H + H * M) ≤
      (4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)))*(2:ℝ)^n :=
    hsNormSq_centeredGrading_anticommutator_le_of_trace_finite_range n d hn P hP H
      (signMatrix_conjTranspose_mul h hh) (signMatrix_mul_conjTranspose h hh) htrace hvanish
  rw [averageSensitivity_eq_parity_edges hf]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr
  calc
    _ ≤ 2*hsNormSq (M*H+H*M) := hedge
    _ ≤ 2*((4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)))*(2:ℝ)^n) :=
      mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = _ := by ring

theorem polynomial_refined_of_nonzero_finite_range {n d : ℕ} (hn : 1 ≤ n)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x : Cube n, polynomialValue p x ≠ 0) :
    averageSensitivity (polynomialThreshold p) ≤
      8*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)) := by
  let w : Cube n → ℝ := fun x => |polynomialValue p x|
  have hw (x : Cube n) : 0 < w x := abs_pos.mpr (hnz x)
  apply sensitivity_finite_range_of_grading hn (polynomialThreshold p)
    (fun x => thresholdSign_cases (polynomialValue p x))
    (weightedProjectionMatrix w hw)
    (weightedProjectionMatrix_family w hw)
    (weightedProjectionMatrix_trace_re w hw)
  · intro i
    exact weightedProjectionMatrix_tridiagonal w hw i
  · intro r s hrs
    exact weightedProjectionMatrix_block_eq_zero_of_polynomial_degree p hp hd hnz r s hrs

/-- Finite-range bound for arbitrary multilinear `p` of degree `≤ d`. -/
theorem polynomial_refined_finite_range {n d : ℕ} (hn : 1 ≤ n)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤
      8*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)) := by
  obtain ⟨q,hq,hqd,hqnz,hqf⟩ := exists_nonzero_polynomial_same_threshold hp hd
  rw [←hqf]
  exact polynomial_refined_of_nonzero_finite_range hn q hq hqd hqnz

/-! ## The Wallis absorption: `mad n·(n+d)/(n+2d) ≤ √n/√(2π)` -/

/-- The uniform block bound at general `n` — the parity split of
`wallis_block_sq_of_even` / `wallis_block_sq_of_odd`.  The odd branch needs
`d ≥ 1` (the odd-n absorption; at `d = 0` the odd value `mad 1 = 1/2` beats
`√(1/2π)`), which is why `hd : 0 < d` is carried. -/
theorem wallis_block_sq (n d : ℕ) (hd : 0 < d) :
    2*Real.pi*(mad n)^2 * ((n:ℝ)+d)^2 ≤ (n:ℝ) * ((n:ℝ)+2*d)^2 := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, rfl⟩ := he
    simpa only [two_mul, Nat.cast_add] using wallis_block_sq_of_even k d
  · obtain ⟨k, rfl⟩ := ho
    simpa only [two_mul, Nat.cast_add, Nat.cast_one] using wallis_block_sq_of_odd k d hd

/-- Square-root form of the block corollary: `mad n·(n+d)/(n+2d) ≤ √n/√(2π)`,
i.e. `√(2π)·b_n·(n+d)/(√n·(n+2d)) ≤ 1` (the paper's last three displays). -/
theorem mad_block_le_sqrt (n d : ℕ) (hd : 0 < d) :
    mad n * ((n:ℝ)+d)/((n:ℝ)+2*d) ≤ Real.sqrt (n:ℝ)/Real.sqrt (2*Real.pi) := by
  have hsq := wallis_block_sq n d hd
  have hden : (0:ℝ) < (n:ℝ)+2*d := by positivity
  have h2pi : (0:ℝ) < 2*Real.pi := by positivity
  have hmad0 : 0 ≤ mad n := by
    unfold mad rawMAD
    positivity
  have hx : 0 ≤ mad n * ((n:ℝ)+d)/((n:ℝ)+2*d) :=
    div_nonneg (mul_nonneg hmad0 (by positivity)) hden.le
  have hcle : (mad n * ((n:ℝ)+d)/((n:ℝ)+2*d))^2 * (2*Real.pi) ≤ (n:ℝ) := by
    have h : (mad n * ((n:ℝ)+d)/((n:ℝ)+2*d))^2
        = (mad n)^2 * ((n:ℝ)+d)^2 / ((n:ℝ)+2*d)^2 := by
      rw [div_pow, mul_pow]
    rw [h, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_ne_zero hden.ne')]
    nlinarith [hsq]
  have hle2 : (mad n * ((n:ℝ)+d)/((n:ℝ)+2*d))^2 ≤ (n:ℝ)/(2*Real.pi) :=
    (le_div_iff₀ h2pi).mpr hcle
  have hsqrt := Real.sqrt_le_sqrt hle2
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx] at hsqrt
  rw [Real.sqrt_div (Nat.cast_nonneg n) (2*Real.pi)] at hsqrt
  exact hsqrt

/-! ## The uniform bound `AS(f) ≤ (8/√(2π))·d·√n` -/

theorem polynomial_bound_sqrt_two_pi {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hdegree : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤
      ((8:ℝ)/Real.sqrt (2*Real.pi))*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have hfin := polynomial_refined_finite_range hn p hp hdegree
  have hdp : 0 < d := by omega
  have habs := mad_block_le_sqrt n d hdp
  have hsqrt_ne : Real.sqrt (2*Real.pi) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).ne'
  have hre : 8*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ))
      = (8*(d:ℝ)) * (mad n * ((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ))) := by
    rw [← mul_div_assoc, mul_assoc]
  calc
    averageSensitivity (polynomialThreshold p) ≤
        8*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)) := hfin
    _ = (8*(d:ℝ)) * (mad n * ((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ))) := hre
    _ ≤ (8*(d:ℝ)) * (Real.sqrt (n:ℝ)/Real.sqrt (2*Real.pi)) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ = ((8:ℝ)/Real.sqrt (2*Real.pi))*(d:ℝ)*Real.sqrt (n:ℝ) := by
      field_simp [hsqrt_ne] <;> ring

/-- Uniform bound for arbitrary `p` (no multilinearity hypothesis), via
`multilinearize`. -/
theorem polynomial_bound_sqrt_two_pi_general {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (p : MvPolynomial (Fin n) ℝ) (hdegree : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤
      ((8:ℝ)/Real.sqrt (2*Real.pi))*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have hsame : polynomialThreshold (multilinearize p) = polynomialThreshold p := by
    funext x
    unfold polynomialThreshold
    rw [multilinearize_value]
  rw [←hsame]
  exact polynomial_bound_sqrt_two_pi hn hd _ (multilinearize_isMultilinear p)
    ((multilinearize_degree_le p).trans hdegree)

/-! ## The rational constant: `399/125` -/

theorem polynomial_bound_399_125 {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hdegree : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ (399/125:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have h := polynomial_bound_sqrt_two_pi hn hd p hp hdegree
  have hd0 : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
  have hdn : 0 ≤ (d:ℝ)*Real.sqrt (n:ℝ) := mul_nonneg hd0 (Real.sqrt_nonneg _)
  have hstep := mul_le_mul_of_nonneg_right (le_of_lt cert_8_div_sqrt_two_pi_lt) hdn
  rw [← mul_assoc, ← mul_assoc] at hstep
  exact h.trans hstep

/-- **Submission-grade uniform bound — the R7 `399/125` theorem.**
For every `p : MvPolynomial (Fin n) ℝ` with `p.totalDegree ≤ d`, `1 ≤ n`, `1 ≤ d`
(no multilinearity hypothesis — `multilinearize` removes it):

`averageSensitivity (polynomialThreshold p) ≤ (399/125)·d·√n`,  `399/125 = 3.192`.

**Assembly map** (which lemma feeds which factor):

* **4 — the coupling/block factor.** `block_coupling_finite_range`
  (BlockRefinement.lean) instantiates the finite-range compensated coupling
  `compensated_coupling_finite_range` (RefinedCoupling.lean — the paper's Lemma 2
  corollary, eq. (6)) at `a = d`, `L = n`, `m = n/2` and bounds the centered
  block sum by `4·d·mad n·(n+d)/(n+2d)·2ⁿ`.  (The at-term form
  `compensated_coupling_at` — Lemma 2 itself, `ED² + a·t ≤ 4ab` — is the engine
  underneath.)
* **2 — the AS(f)-level factor** (paper eq. (16)).  The edge comparison
  `edge_recovery` / `normalized_edge_bound` (OAI/Combinatorics/GotsmanLinial/)
  gives `|E(h)| ≤ 2·‖M*H+H*M‖²_HS`; with `averageSensitivity_eq_parity_edges`
  this doubles the block constant to `8·d·mad n·(n+d)/(n+2d)` — see
  `sensitivity_finite_range_of_grading` → `polynomial_refined_finite_range`.
* **Wallis absorption.** `wallis_block_sq_of_even` / `wallis_block_sq_of_odd`
  (WallisMAD.lean — paper eqs. (18)–(19), the increasing-sequence Wallis bound
  `central k² ≤ 4/(π(4k+1))`) give `2π·(mad n)²·(n+d)² ≤ n·(n+2d)²`, i.e.
  `mad n·(n+d)/(n+2d) ≤ √n/√(2π)` (`mad_block_le_sqrt`).  Times `8d`:
  `AS(f) ≤ (8/√(2π))·d·√n` (`polynomial_bound_sqrt_two_pi`).
* **the rational constant.** `cert_8_div_sqrt_two_pi_lt` (WallisMAD.lean):
  `8/√(2π) < 399/125`.  Squared, the certificate needs only
  `π > 500000/159201 ≈ 3.14068`; the **exact π margin** used is Mathlib's
  `Real.pi_gt_d4` (`3.1415 < π`) — the arctan(1/2)+arctan(1/3) route is
  unnecessary.

**Odd-n handling.** `wallis_block_sq_of_even` covers `n = 2k` for every `d`
(including `k = 0`); `wallis_block_sq_of_odd` covers `n = 2k+1` and needs
`d ≥ 1` — the odd-n absorption, since at `d = 0` the odd value `mad 1 = 1/2`
beats `√(1/2π)`.  The hypothesis `hd : 1 ≤ d` supplies it (degree-`0` thresholds
have `AS = 0` and are covered by the bound trivially through the same statement),
and `wallis_block_sq` is the parity split that feeds `mad_block_le_sqrt`.

Chain: `AS(f) ≤ 8·d·mad n·(n+d)/(n+2d) ≤ (8/√(2π))·d·√n < (399/125)·d·√n`. -/
theorem AS_bound_399_125 {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (p : MvPolynomial (Fin n) ℝ) (hdegree : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ (399/125:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have hsame : polynomialThreshold (multilinearize p) = polynomialThreshold p := by
    funext x
    unfold polynomialThreshold
    rw [multilinearize_value]
  rw [←hsame]
  exact polynomial_bound_399_125 hn hd _ (multilinearize_isMultilinear p)
    ((multilinearize_degree_le p).trans hdegree)

/-- Tree-convention alias of `AS_bound_399_125`, mirroring
`polynomial_bound_3762_general`'s naming. -/
theorem polynomial_bound_399_125_general {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (p : MvPolynomial (Fin n) ℝ) (hdegree : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ (399/125:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) :=
  AS_bound_399_125 hn hd p hdegree

end AverageSensitivity
