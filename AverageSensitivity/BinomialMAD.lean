import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators
namespace AverageSensitivity

noncomputable def rawMAD (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*|2*(j:ℝ)-(n:ℝ)|

theorem abs_walk_step (n j : ℕ) :
    |2*(j:ℝ)-(n:ℝ)-1|+|2*(j:ℝ)-(n:ℝ)+1| =
      2*|2*(j:ℝ)-(n:ℝ)| + if 2*j=n then 2 else 0 := by
  split_ifs with h
  · have he : 2*(j:ℝ)=(n:ℝ) := by exact_mod_cast h
    norm_num [he]
  · by_cases hlt : 2*j<n
    · have hr : 2*(j:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
      ring
    · have hgt : n+1≤2*j := by omega
      have hr : (n:ℝ)+1≤2*(j:ℝ) := by exact_mod_cast hgt
      rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
      ring

theorem rawMAD_succ (n : ℕ) :
    rawMAD (n+1) = 2*rawMAD n +
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*(if 2*j=n then 2 else 0) := by
  unfold rawMAD
  rw [Finset.sum_choose_succ_mul (fun j _ => |2*(j:ℝ)-((n+1:ℕ):ℝ)|) n]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*
        (2*|2*(j:ℝ)-(n:ℝ)|+(if 2*j=n then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      have h := abs_walk_step n j
      have he : 2*((j:ℝ)+1)-((n:ℝ)+1)=2*(j:ℝ)-(n:ℝ)+1 := by ring
      rw [he]
      rw [show 2*(j:ℝ)-((n:ℝ)+1)=2*(j:ℝ)-(n:ℝ)-1 by ring]
      rw [← mul_add, h]
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intros
      ring

theorem rawMAD_succ_even (k : ℕ) :
    rawMAD (2*k+1) = 2*rawMAD (2*k)+2*((2*k).choose k : ℝ) := by
  rw [rawMAD_succ]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
    ring
  · intro j _ hj
    have h : ¬2*j=2*k := by omega
    simp [h]
  · simp
    omega

theorem rawMAD_succ_odd (k : ℕ) :
    rawMAD (2*k+2) = 2*rawMAD (2*k+1) := by
  have h := rawMAD_succ (2*k+1)
  have hz : (∑ j ∈ Finset.range (2*k+1+1), ((2*k+1).choose j : ℝ)*
      (if 2*j=2*k+1 then 2 else 0))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have he : ¬2*j=2*k+1 := by omega
    simp [he]
  simpa only [hz,add_zero] using h

theorem rawMAD_even (k : ℕ) :
    rawMAD (2*k) = 2*(k:ℝ)*(Nat.centralBinom k : ℝ) := by
  induction k with
  | zero => norm_num [rawMAD, Nat.centralBinom]
  | succ k ih =>
    have he := rawMAD_succ_even k
    have ho := rawMAD_succ_odd k
    have hc : ((k:ℝ)+1)*(Nat.centralBinom (k+1):ℝ) =
        2*(2*(k:ℝ)+1)*(Nat.centralBinom k:ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    rw [show 2*(k+1)=2*k+2 by omega,ho,he,ih]
    simp only [Nat.cast_add,Nat.cast_one,Nat.centralBinom] at *
    nlinarith

theorem rawMAD_odd (k : ℕ) :
    rawMAD (2*k+1) = 2*(2*(k:ℝ)+1)*(Nat.centralBinom k : ℝ) := by
  rw [rawMAD_succ_even,rawMAD_even]
  simp only [Nat.centralBinom]
  ring

noncomputable def central (k : ℕ) : ℝ := (Nat.centralBinom k:ℝ)/(4:ℝ)^k
noncomputable def mad (n : ℕ) : ℝ := rawMAD n/(2*(2:ℝ)^n)

theorem mad_even (k : ℕ) : mad (2*k) = (k:ℝ)*central k := by
  simp only [mad,rawMAD_even,central,pow_mul]
  norm_num
  ring

theorem mad_odd (k : ℕ) : mad (2*k+1) = (2*(k:ℝ)+1)*central k/2 := by
  simp only [mad,rawMAD_odd,central,pow_add,pow_mul]
  norm_num
  ring

theorem mad_zero : mad 0 = 0 := by
  simp [mad, rawMAD]

theorem mad_nonneg (n : ℕ) : 0 ≤ mad n := by
  unfold mad rawMAD
  refine div_nonneg (Finset.sum_nonneg fun j _ => ?_) (by positivity)
  exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

theorem central_step (k : ℕ) :
    (2*(k:ℝ)+2)*central (k+1) = (2*(k:ℝ)+1)*central k := by
  have hc : ((k:ℝ)+1)*(Nat.centralBinom (k+1):ℝ) =
        2*(2*(k:ℝ)+1)*(Nat.centralBinom k:ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  unfold central
  rw [pow_succ]
  field_simp
  nlinarith

end AverageSensitivity
