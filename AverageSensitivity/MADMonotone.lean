import AverageSensitivity.BinomialMAD

/-!
# The tail weight: exact monotonicity, no affine majorant

`ConstantExtraction.central_tail` bounds `central k ^ 2` by an affine function of `k` with slack
parameters `(785147/250000, 402203/500000)`, and `mad_tail_squared` converts that into
`64 * mad n ^ 2 ≤ K * n`. The resulting `K` is loose because the affine majorant is strictly
worse than `central` itself.

The weight that actually governs the tail constant is

    tailWeight n = 64 * (mad n) ^ 2 / n .

Its exact structure, from `central_step` alone (both cases are a one-line arithmetic gap of 1):

* **odd subsequence decreases**:  `w (2k+3) / w (2k+1) = (2k+1)(2k+3)/(2k+2)^2 < 1`
* **even sits below the preceding odd**: `w (2k+2) / w (2k+1) = (2k+1)/(2k+2) < 1`
* **even subsequence increases**: `w (2k+2) / w (2k) = (2k+1)^2/(4k(k+1)) > 1`
  (note the direction — this one is *not* decreasing; see `BOARD-INTEL.md` §8)

Hence every even value lies below the odd value just before it, and the odd values decrease, so

    sup { tailWeight n | N ≤ n } = tailWeight N  (N odd)   =   tailWeight (N+1)  (N even).

So the optimal tail constant is a single exact rational evaluation at the window start, no case
analysis over the window, and `central_tail` is not needed at all.
-/

open scoped BigOperators
namespace AverageSensitivity

/-- The tail weight. Its supremum over `n ≥ N` is the optimal `K` for the large-`n` branch. -/
noncomputable def tailWeight (n : ℕ) : ℝ := 64*(mad n)^2/(n:ℝ)

/-- `central (k+1) = (2k+1)/(2k+2) * central k`, from `central_step`. -/
theorem central_succ_ratio (k : ℕ) :
    central (k+1) = (2*(k:ℝ)+1)/(2*(k:ℝ)+2) * central k := by
  have hc := central_step k
  have h2 : (2*(k:ℝ)+2) ≠ 0 := by positivity
  have h : central (k+1) * (2*(k:ℝ)+2) = (2*(k:ℝ)+1) * central k := by
    rw [mul_comm]; exact hc
  rw [div_mul_eq_mul_div, eq_div_iff h2, h]

/-- The same relation squared, **without any division**: the form `nlinarith` can use. -/
theorem sq_central_succ_mul (k : ℕ) :
    (2*(k:ℝ)+2)^2 * (central (k+1))^2 = (2*(k:ℝ)+1)^2 * (central k)^2 := by
  have hc := central_step k
  have h := congrArg (fun x : ℝ => x^2) hc
  rw [mul_pow, mul_pow] at h
  exact h

/-- **Odd subsequence decreases**: `w (2k+3) ≤ w (2k+1)`. -/
theorem tailWeight_odd_step (k : ℕ) :
    tailWeight (2*k+3) ≤ tailWeight (2*k+1) := by
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hcs := sq_central_succ_mul k
  unfold tailWeight
  rw [show 2*k+3 = 2*(k+1)+1 by ring, mad_odd, mad_odd]
  push_cast
  rw [div_pow, mul_pow, div_pow, mul_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcs, sq_nonneg (central k), sq_nonneg (central (k+1)),
    sq_nonneg (2*(k:ℝ)+1), sq_nonneg (2*(k:ℝ)+3), hk0]

/-- **Every even value sits below the odd value just before it**: `w (2k+2) ≤ w (2k+1)`. -/
theorem tailWeight_even_le_odd (k : ℕ) :
    tailWeight (2*k+2) ≤ tailWeight (2*k+1) := by
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hcs := sq_central_succ_mul k
  unfold tailWeight
  rw [show 2*k+2 = 2*(k+1) by ring, mad_even, mad_odd]
  push_cast
  rw [mul_pow, div_pow, mul_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcs, sq_nonneg (central k), sq_nonneg (central (k+1)),
    sq_nonneg (2*(k:ℝ)+1), hk0, hk1]
/-- **Every even value sits below the FOLLOWING odd value**: `w (2k+2) ≤ w (2k+3)`. -/
theorem tailWeight_even_le_next_odd (k : ℕ) :
    tailWeight (2*k+2) ≤ tailWeight (2*k+3) := by
  have hc2 : (0:ℝ) ≤ (central (k+1))^2 := sq_nonneg _
  have hxy : (0:ℝ) ≤ ((k:ℝ)+1)*(2*(k:ℝ)+3) := by positivity
  unfold tailWeight
  rw [show 2*k+2 = 2*(k+1) by ring, show 2*k+3 = 2*(k+1)+1 by ring,
    mad_even, mad_odd]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hc2, hxy, mul_nonneg hxy hc2]

/-- **The tail weight above 21 is maximised at 21 itself.** -/
theorem tailWeight_le_tailWeight_21 : ∀ j : ℕ, 21 ≤ j → tailWeight j ≤ tailWeight 21 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases h21 : j = 21
    · rw [h21]
    · have h22 : 22 ≤ j := by omega
      rcases Nat.eq_or_lt_of_le h22 with h22' | h22'
      · -- j = 22: the even value below its preceding odd (= 21)
        subst h22'
        exact tailWeight_even_le_odd 10
      · rcases Nat.eq_or_lt_of_le h22' with h23' | h23'
        · -- j = 23: one odd step down
          subst h23'
          exact tailWeight_odd_step 10
        · -- j ≥ 24: step down and recurse
          have hj4 : 24 ≤ j := by omega
          rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
          · rw [hk] at hj4 ih ⊢
            have hk1 : 1 ≤ k := by omega
            have hstep := tailWeight_even_le_odd (k-1)
            rw [show 2*(k-1)+2 = 2*k by omega,
                show 2*(k-1)+1 = 2*k-1 by omega] at hstep
            have hrec := ih (2*k-1) (by omega) (by omega)
            rw [show k + k = 2*k by omega]
            exact hstep.trans hrec
          · rw [hk] at hj4 ih ⊢
            have hk1 : 1 ≤ k := by omega
            have hstep := tailWeight_odd_step (k-1)
            rw [show 2*(k-1)+3 = 2*k+1 by omega,
                show 2*(k-1)+1 = 2*k-1 by omega] at hstep
            have hrec := ih (2*k-1) (by omega) (by omega)
            exact hstep.trans hrec

/-- The exact value of the sharp tail constant: `w 21 = 44801898141 / 2^32`. -/
theorem tailWeight_21_eq : tailWeight 21 = (44801898141/4294967296:ℝ) := by
  have hc10 : central 10 = (184756:ℝ)/1048576 := by
    unfold central
    have hcb : Nat.centralBinom 10 = 184756 := by decide
    rw [hcb]
    norm_num
  unfold tailWeight
  rw [show (21:ℕ) = 2*10+1 by norm_num, mad_odd, hc10]
  norm_num

/-- **The sharp tail bound**: `64 * mad n ^ 2 ≤ K* * n` for `n ≥ 20`, where the
optimal constant is the exact rational `K* = 44801898141 / 2^32` — the value of
`tailWeight 21` (the supremum), not an affine majorant with slack. -/
theorem mad_tail_squared_sharp (n : ℕ) (hn : 20 ≤ n) :
    64*(mad n)^2 ≤ (44801898141/4294967296:ℝ)*(n:ℝ) := by
  have hn0 : (0:ℝ) < ((n:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h : tailWeight n ≤ tailWeight 21 := by
    rcases Nat.eq_or_lt_of_le hn with h20 | h21n
    · subst h20
      exact tailWeight_even_le_next_odd 9
    · exact tailWeight_le_tailWeight_21 n h21n
  rw [tailWeight_21_eq] at h
  unfold tailWeight at h
  rw [div_le_div_iff₀ hn0 (by positivity : (0:ℝ) < 4294967296)] at h
  rw [show (44801898141/4294967296:ℝ)*((n:ℕ):ℝ) =
      44801898141*((n:ℕ):ℝ)/(4294967296:ℝ) by ring]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4294967296)]
  exact h

end AverageSensitivity
