import OAI.Combinatorics.GotsmanLinial.Main
import AverageSensitivity.BlockRefinement
import AverageSensitivity.ConstantExtraction

open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial
namespace AverageSensitivity

theorem sensitivity_refined_of_grading {n d : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (P : Fin (n + 1) → Matrix (Cube n) (Cube n) ℂ)
    (hP : OrthogonalProjectionFamily P)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (htri : ∀ i : Fin n, BlockTridiagonal P (coordinateSignMatrix i))
    (hvanish : ∀ r s : Fin (n + 1), r.val + s.val < n - d →
      P s * signMatrix (fun x => fullParity x * f x) * P r = 0) :
    averageSensitivity f ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2 := by
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
      (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n :=
    hsNormSq_centeredGrading_anticommutator_le_of_trace n d P hP H
      (signMatrix_conjTranspose_mul h hh) (signMatrix_mul_conjTranspose h hh) htrace hvanish
  rw [averageSensitivity_eq_parity_edges hf]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr
  calc
    _ ≤ 2*hsNormSq (M*H+H*M) := hedge
    _ ≤ 2*((4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n) :=
      mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = _ := by ring

theorem polynomial_refined_of_nonzero {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x : Cube n, polynomialValue p x ≠ 0) :
    averageSensitivity (polynomialThreshold p) ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2 := by
  let w : Cube n → ℝ := fun x => |polynomialValue p x|
  have hw (x : Cube n) : 0 < w x := abs_pos.mpr (hnz x)
  apply sensitivity_refined_of_grading (polynomialThreshold p)
    (fun x => thresholdSign_cases (polynomialValue p x))
    (weightedProjectionMatrix w hw)
    (weightedProjectionMatrix_family w hw)
    (weightedProjectionMatrix_trace_re w hw)
  · intro i
    exact weightedProjectionMatrix_tridiagonal w hw i
  · intro r s hrs
    exact weightedProjectionMatrix_block_eq_zero_of_polynomial_degree p hp hd hnz r s hrs

theorem polynomial_refined {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2 := by
  obtain ⟨q,hq,hqd,hqnz,hqf⟩ := exists_nonzero_polynomial_same_threshold hp hd
  rw [←hqf]
  exact polynomial_refined_of_nonzero q hq hqd hqnz

theorem averageSensitivity_le_dimension {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f ≤ (n:ℝ) := by
  classical
  have hcard (i : Fin n) : ((sensitiveVertices f i).card:ℝ) ≤ (2:ℝ)^n := by
    have h : (sensitiveVertices f i).card ≤ Fintype.card (Cube n) := Finset.card_le_univ _
    simpa only [card_cube,Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr h
  calc
    _ ≤ ∑ i : Fin n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (div_le_one (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr (hcard i)
    _ = _ := by simp

theorem polynomial_bound_3762 {n d : ℕ} (hn : 1≤n) (hd : 1≤d)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hdegree : p.totalDegree≤d) :
    averageSensitivity (polynomialThreshold p) ≤ (37619/10000:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  exact extract_constant n d hn hd _ (averageSensitivity_le_dimension _) (polynomial_refined p hp hdegree)

end AverageSensitivity
