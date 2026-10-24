import AverageSensitivity.PolynomialBound

open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial
namespace AverageSensitivity

noncomputable def parityExponent {n : ℕ} (m : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  m.mapRange (fun e => e%2) (by decide)

noncomputable def multilinearize {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial (parityExponent m) (MvPolynomial.coeff m p)

theorem multilinearize_isMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsMultilinear (multilinearize p) := by
  classical
  intro m hm i
  obtain ⟨s,hs,hms⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have he : m=parityExponent s := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hms)
  rw [he]
  simp only [parityExponent,Finsupp.mapRange_apply]
  omega

theorem parityExponent_degree_le {n : ℕ} (m : Fin n →₀ ℕ) :
    (parityExponent m).sum (fun _ e => e) ≤ m.sum (fun _ e => e) := by
  rw [Finsupp.sum_fintype _ _ (by simp),Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  intro i _
  simp only [parityExponent,Finsupp.mapRange_apply]
  exact Nat.mod_le _ _

theorem multilinearize_degree_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    (multilinearize p).totalDegree ≤ p.totalDegree := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    ((parityExponent_degree_le m).trans (MvPolynomial.le_totalDegree hm))

theorem sign_pow_mod_two (x : ℝ) (hx : x=1 ∨ x= -1) (e : ℕ) : x^(e%2)=x^e := by
  rcases hx with rfl | rfl
  · simp
  · have he : e=e%2+2*(e/2) := by omega
    conv_rhs => rw [he,pow_add,pow_mul]
    norm_num

theorem multilinearize_value {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Cube n) :
    polynomialValue (multilinearize p) x = polynomialValue p x := by
  classical
  unfold polynomialValue multilinearize
  rw [map_sum]
  conv_rhs => rw [p.as_sum,map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval_monomial,MvPolynomial.eval_monomial]
  congr 1
  rw [parityExponent,Finsupp.prod_mapRange_index (by simp)]
  apply Finset.prod_congr rfl
  intro i _
  exact sign_pow_mod_two _ (cubeCoord_cases x i) _

theorem polynomial_bound_3762_general {n d : ℕ} (hn : 1≤n) (hd : 1≤d)
    (p : MvPolynomial (Fin n) ℝ) (hdegree : p.totalDegree≤d) :
    averageSensitivity (polynomialThreshold p) ≤ (75231/20000:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have hsame : polynomialThreshold (multilinearize p) = polynomialThreshold p := by
    funext x
    unfold polynomialThreshold
    rw [multilinearize_value]
  rw [←hsame]
  exact polynomial_bound_3762 hn hd _ (multilinearize_isMultilinear p)
    ((multilinearize_degree_le p).trans hdegree)

end AverageSensitivity
