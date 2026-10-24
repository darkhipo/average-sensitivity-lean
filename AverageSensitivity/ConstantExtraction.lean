import AverageSensitivity.BinomialMAD

open scoped BigOperators
namespace AverageSensitivity

theorem central_tail (k : ℕ) (hk : 10 ≤ k) :
    central k ^ 2 * ((785147/250000:ℝ)*(k:ℝ)+402203/500000) ≤ 1 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [central, Nat.centralBinom, Nat.choose]
  | succ k hk ih =>
    have hc := central_step k
    have hkR : (10:ℝ)≤(k:ℝ) := by exact_mod_cast hk
    have hgap : 0 ≤ (2*(k:ℝ)+2)^2*((785147/250000:ℝ)*(k:ℝ)+402203/500000) -
        (2*(k:ℝ)+1)^2*((785147/250000:ℝ)*((k:ℝ)+1)+402203/500000) := by
      nlinarith
    have hmul := mul_nonneg (sq_nonneg (central k)) hgap
    have hpos : 0 < (2*(k:ℝ)+2)^2 := sq_pos_of_pos (by positivity)
    have he : (2*(k:ℝ)+2)^2 * (central (k+1)^2 *
        ((785147/250000:ℝ)*((k:ℝ)+1)+402203/500000)) =
        central k^2*((2*(k:ℝ)+1)^2*((785147/250000:ℝ)*((k:ℝ)+1)+402203/500000)) := by
      calc
        _ = ((2*(k:ℝ)+2)*central (k+1))^2 *
            ((785147/250000:ℝ)*((k:ℝ)+1)+402203/500000) := by ring
        _ = ((2*(k:ℝ)+1)*central k)^2 *
            ((785147/250000:ℝ)*((k:ℝ)+1)+402203/500000) := by rw [hc]
        _ = _ := by ring
    have hi := mul_le_mul_of_nonneg_left ih hpos.le
    push_cast
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [he]

theorem mad_nonneg (n : ℕ) : 0 ≤ mad n := by
  unfold mad rawMAD
  positivity

theorem mad_tail_squared (n : ℕ) (hn : 20 ≤ n) :
    64*mad n^2 ≤ (168000000/16105143:ℝ)*(n:ℝ) := by
  let k := n/2
  have hk : 10 ≤ k := by dsimp [k]; omega
  have hkR : (10:ℝ)≤(k:ℝ) := by exact_mod_cast hk
  have htail := central_tail k hk
  have hL : 0≤(785147/250000:ℝ)*(k:ℝ)+402203/500000 := by positivity
  have hcentral : 0≤central k^2 := sq_nonneg _
  have hform : n=2*k ∨ n=2*k+1 := by dsimp [k]; omega
  rcases hform with he | ho
  · rw [he,mad_even]
    push_cast
    have hlinear : 64*(k:ℝ)^2 ≤ (168000000/16105143:ℝ)*(2*(k:ℝ))*
        ((785147/250000:ℝ)*(k:ℝ)+402203/500000) := by nlinarith [sq_nonneg (k:ℝ)]
    calc
      _ = 64*(k:ℝ)^2*central k^2 := by ring
      _ ≤ ((168000000/16105143:ℝ)*(2*(k:ℝ))*((785147/250000:ℝ)*(k:ℝ)+402203/500000))*central k^2 :=
        mul_le_mul_of_nonneg_right hlinear hcentral
      _ = (168000000/16105143:ℝ)*(2*(k:ℝ))*(central k^2*((785147/250000:ℝ)*(k:ℝ)+402203/500000)) := by ring
      _ ≤ (168000000/16105143:ℝ)*(2*(k:ℝ))*1 := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  · rw [ho,mad_odd]
    push_cast
    have hlinear : 16*(2*(k:ℝ)+1) ≤ (168000000/16105143:ℝ)*
        ((785147/250000:ℝ)*(k:ℝ)+402203/500000) := by nlinarith
    have hlinear2 := mul_le_mul_of_nonneg_right hlinear (show 0≤2*(k:ℝ)+1 by positivity)
    calc
      _ = (16*(2*(k:ℝ)+1)*(2*(k:ℝ)+1))*central k^2 := by ring
      _ ≤ ((168000000/16105143:ℝ)*((785147/250000:ℝ)*(k:ℝ)+402203/500000)*(2*(k:ℝ)+1))*central k^2 :=
        mul_le_mul_of_nonneg_right hlinear2 hcentral
      _ = (168000000/16105143:ℝ)*(2*(k:ℝ)+1)*(central k^2*((785147/250000:ℝ)*(k:ℝ)+402203/500000)) := by ring
      _ ≤ (168000000/16105143:ℝ)*(2*(k:ℝ)+1)*1 := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring

theorem small_numeric (n : ℕ) (hn : 15 ≤ n) (hn' : n < 20) :
    (8*mad n+2)^2 ≤ (37615399/10000000:ℝ)^2*(n:ℝ) := by
  interval_cases n <;>
    norm_num [mad,rawMAD,Finset.sum_range_succ,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem extract_constant (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (A : ℝ) (htrivial : A ≤ (n:ℝ))
    (hrefined : A ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2) :
    A ≤ (37615399/10000000:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have hs0 := Real.sqrt_nonneg (n:ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have hn0 : (0:ℝ)≤(n:ℝ) := Nat.cast_nonneg n
  have hd0 : (1:ℝ)≤(d:ℝ) := by exact_mod_cast hd
  by_cases ht : (n:ℝ) ≤ (37615399/10000000:ℝ)^2*(d:ℝ)^2
  · have hscale : Real.sqrt (n:ℝ) ≤ (37615399/10000000:ℝ)*(d:ℝ) := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hscale hs0
    nlinarith
  · have hscale : (37615399/10000000:ℝ)*(d:ℝ) < Real.sqrt (n:ℝ) := by
      nlinarith
    by_cases hlarge : 20 ≤ n
    · have hm2 := mad_tail_squared n hlarge
      have hm0 := mad_nonneg n
      have hcoef : (168000000/16105143:ℝ) < (37615399/10000000-2/(37615399/10000000):ℝ)^2 := by norm_num
      have hmn := mul_le_mul_of_nonneg_right hcoef.le hn0
      have hmad : 8*mad n ≤ (37615399/10000000-2/(37615399/10000000):ℝ)*Real.sqrt (n:ℝ) := by
        have hsquare : (8*mad n)^2 ≤
            ((37615399/10000000-2/(37615399/10000000):ℝ)*Real.sqrt (n:ℝ))^2 := by
          simp only [mul_pow,hs2]
          nlinarith
        have hpos : 0 ≤ (37615399/10000000-2/(37615399/10000000):ℝ)*Real.sqrt (n:ℝ) := by positivity
        nlinarith
      have hi : 8*mad n+2*(d:ℝ) ≤ (37615399/10000000:ℝ)*Real.sqrt (n:ℝ) := by
        nlinarith
      have hm := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg d)
      nlinarith
    · have hnR : (n:ℝ)≤19 := by exact_mod_cast (show n≤19 by omega)
      have hd1 : d=1 := by
        by_contra he
        have hd2 : (2:ℝ)≤(d:ℝ) := by exact_mod_cast (show 2≤d by omega)
        nlinarith [sq_nonneg ((d:ℝ)-2)]
      subst d
      norm_num at ht hscale hrefined ⊢
      have hn15 : 15≤n := by
        have : (14:ℝ)<(n:ℝ) := by nlinarith
        exact_mod_cast this
      have hm2 := small_numeric n hn15 (by omega)
      have hm0 := mad_nonneg n
      have hsquare : (8*mad n+2)^2 ≤ ((37615399/10000000:ℝ)*Real.sqrt (n:ℝ))^2 := by
        rw [mul_pow,hs2]
        exact hm2
      have hpos : 0≤(37615399/10000000:ℝ)*Real.sqrt (n:ℝ) := by positivity
      nlinarith

end AverageSensitivity
