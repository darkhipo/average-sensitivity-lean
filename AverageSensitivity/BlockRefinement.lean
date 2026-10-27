import OAI.Combinatorics.GotsmanLinial.BlockCoupling
import AverageSensitivity.RefinedCoupling
import AverageSensitivity.ChargeMass
import AverageSensitivity.BinomialMAD

open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial
namespace AverageSensitivity

theorem binomial_mad_eq (n : ℕ) :
    (∑ s : Fin (n+1), binomialWeight n s * |(s.val:ℝ)-(n:ℝ)/2|) = mad n := by
  simp only [binomialWeight]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (n.choose j:ℝ)/(2:ℝ)^n*|(j:ℝ)-(n:ℝ)/2|)]
  unfold mad rawMAD
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have he : |2*(j:ℝ)-(n:ℝ)| = 2*|(j:ℝ)-(n:ℝ)/2| := by
    rw [show 2*(j:ℝ)-(n:ℝ) = 2*((j:ℝ)-(n:ℝ)/2) by ring,abs_mul]
    norm_num
  rw [he]
  ring

theorem block_coupling_refined
    (n d : ℕ) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by
  let w : Fin (n + 1) × Fin (n + 1) → ℝ :=
    normalizedPairWeight B ((2 : ℝ) ^ n)
  let U : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => (t.2.val : ℝ)
  let V : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun t => (n : ℝ) - (t.1.val : ℝ)
  have hU (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (U t)) =
        ∑ s : Fin (n + 1), binomialWeight n s * φ (s.val : ℝ) := by
    simpa only [w, U, hcol, binomialWeight] using
      normalizedPairWeight_expect_snd B ((2 : ℝ) ^ n)
        (fun s => φ (s.val : ℝ))
  have hV (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (V t)) =
        ∑ r : Fin (n + 1),
          binomialWeight n r * φ ((n : ℝ) - (r.val : ℝ)) := by
    simpa only [w, V, hrow, binomialWeight] using
      normalizedPairWeight_expect_fst B ((2 : ℝ) ^ n)
        (fun r => φ ((n : ℝ) - (r.val : ℝ)))
  have hw : ∀ t, 0 ≤ w t :=
    normalizedPairWeight_nonneg B _ hB (binomialDenominator_pos n).le
  have hprob : (∑ t, w t) = 1 := by
    have h := hU (fun _ => 1)
    simpa only [mul_one, sum_binomialWeight] using h
  have hsame : ∀ φ : ℝ → ℝ,
      (∑ t, w t * φ (U t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hU, hV, binomialWeight_reflect]
  have hstep : ∀ t, w t ≠ 0 → V t - U t ≤ (d : ℝ) := by
    rintro ⟨r, s⟩ ht
    have hnonzero : B r s ≠ 0 := by
      intro hz
      exact ht (by simp only [w, normalizedPairWeight, hz, zero_div])
    have hnat : n - d ≤ r.val + s.val :=
      Nat.le_of_not_gt (fun hlt => hnonzero (hvanish r s hlt))
    have hnat' : n ≤ r.val + s.val + d := by omega
    have hreal : (n : ℝ) ≤ (r.val : ℝ) + (s.val : ℝ) + (d : ℝ) := by
      exact_mod_cast hnat'
    dsimp only [U, V]
    linarith
  have hbound := finite_coupling_refined w U V ((n:ℝ)/2) (d:ℝ)
    hw hprob hsame (Nat.cast_nonneg d) hstep
  have hmad : (∑ t, w t*|U t-(n:ℝ)/2|)=mad n := by
    rw [hU (fun z => |z-(n:ℝ)/2|),binomial_mad_eq]
  rw [hmad] at hbound
  calc
    _ = (2 : ℝ) ^ n * (∑ t, w t * (U t - V t) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [w, U, V, normalizedPairWeight]
      field_simp [binomialDenominator_ne_zero n]
      ring
    _ ≤ (2 : ℝ) ^ n * (4*(d:ℝ)*mad n+(d:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hbound (binomialDenominator_pos n).le
    _ = (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by ring

/-- The actual finite probability weights supplied by the Hilbert--Schmidt
blocks of an operator in a binomial orthogonal grading. -/
noncomputable def blockCouplingWeight {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  normalizedPairWeight (fun r s => hsNormSq (P s * H * P r)) ((2 : ℝ) ^ n) t

theorem blockCouplingWeight_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : 0 ≤ blockCouplingWeight P H t :=
  normalizedPairWeight_nonneg _ _ (fun _ _ => hsNormSq_nonneg _)
    (binomialDenominator_pos n).le t

/-- The first block index has the binomial distribution. -/
theorem blockCouplingWeight_fst_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (r : Fin (n + 1)) :
    (∑ s : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n r := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_row, sum_hsNormSq_blocks_column hP H r hH, hmult]
  rfl

/-- The second block index has the same binomial distribution. -/
theorem blockCouplingWeight_snd_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (s : Fin (n + 1)) :
    (∑ r : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n s := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_column, sum_hsNormSq_blocks_row hP H s hH, hmult]
  rfl

/-- Unitarity and the grading multiplicities make the block weights a
probability distribution without any additional normalization assumption. -/
theorem sum_blockCouplingWeight {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ)) :
    (∑ t : Fin (n + 1) × Fin (n + 1), blockCouplingWeight P H t) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [blockCouplingWeight_fst_marginal hP H hH hmult]
  exact sum_binomialWeight n

/-- A nonzero block probability lies on or above the required anti-diagonal. -/
theorem blockCouplingWeight_support {n d : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0)
    (r s : Fin (n + 1)) (ht : blockCouplingWeight P H (r, s) ≠ 0) :
    n - d ≤ r.val + s.val := by
  apply Nat.le_of_not_gt
  intro hlt
  apply ht
  simp only [blockCouplingWeight, normalizedPairWeight, hvanish r s hlt,
    hsNormSq_zero, zero_div]

/-- The spectral block coupling bounds the actual centered grading
anticommutator.  Its hypotheses are the orthogonal grading, its binomial
multiplicities, unitarity, and the separately proved low-degree vanishing. -/
theorem hsNormSq_centeredGrading_anticommutator_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by
  rw [hsNormSq_centered_anticommutator hP H]
  apply block_coupling_refined n d (fun r s => hsNormSq (P s * H * P r))
  · intro r s
    exact hsNormSq_nonneg _
  · intro r
    rw [sum_hsNormSq_blocks_column hP H r hleft, hmult]
  · intro s
    rw [sum_hsNormSq_blocks_row hP H s hright, hmult]
  · intro r s hrs
    rw [hvanish r s hrs, hsNormSq_zero]

/-- Trace-multiplicity form, for direct use with finite-dimensional orthogonal
projections whose ranks have already been computed. -/
theorem hsNormSq_centeredGrading_anticommutator_le_of_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by
  apply hsNormSq_centeredGrading_anticommutator_le n d P hP H hleft hright _ hvanish
  intro k
  rw [hsNormSq_projection (P k) (hP.conjTranspose_eq k) (hP.idempotent k), htrace]

/-- The d=1 charged block coupling: the additive slack is not the uniform
`2d^2 = 2` but the forward-charge mass, which equal marginals pin to
`n/(n+1)`. This is the wall-breaking bound of the 3.7614546 submission. -/
theorem block_coupling_refined_d1
    (n : ℕ) (hn : 1 ≤ n) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - 1 → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        (4*mad n + (n:ℝ)/((n:ℝ)+1))*(2:ℝ)^n := by
  let w : Fin (n + 1) × Fin (n + 1) → ℝ :=
    normalizedPairWeight B ((2 : ℝ) ^ n)
  let U : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => (t.2.val : ℝ)
  let V : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun t => (n : ℝ) - (t.1.val : ℝ)
  have hU (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (U t)) =
        ∑ s : Fin (n + 1), binomialWeight n s * φ (s.val : ℝ) := by
    simpa only [w, U, hcol, binomialWeight] using
      normalizedPairWeight_expect_snd B ((2 : ℝ) ^ n)
        (fun s => φ (s.val : ℝ))
  have hV (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (V t)) =
        ∑ r : Fin (n + 1),
          binomialWeight n r * φ ((n : ℝ) - (r.val : ℝ)) := by
    simpa only [w, V, hrow, binomialWeight] using
      normalizedPairWeight_expect_fst B ((2 : ℝ) ^ n)
        (fun r => φ ((n : ℝ) - (r.val : ℝ)))
  have hw : ∀ t, 0 ≤ w t :=
    normalizedPairWeight_nonneg B _ hB (binomialDenominator_pos n).le
  have hprob : (∑ t, w t) = 1 := by
    have h := hU (fun _ => 1)
    simpa only [mul_one, sum_binomialWeight] using h
  have hsame : ∀ φ : ℝ → ℝ,
      (∑ t, w t * φ (U t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hU, hV, binomialWeight_reflect]
  have hstep : ∀ t, w t ≠ 0 → V t - U t ≤ 1 := by
    rintro ⟨r, s⟩ ht
    have hnonzero : B r s ≠ 0 := by
      intro hz
      exact ht (by simp only [w, normalizedPairWeight, hz, zero_div])
    have hnat : n - 1 ≤ r.val + s.val :=
      Nat.le_of_not_gt (fun hlt => hnonzero (hvanish r s hlt))
    have hnat' : n ≤ r.val + s.val + 1 := by omega
    have hreal : (n : ℝ) ≤ (r.val : ℝ) + (s.val : ℝ) + 1 := by
      exact_mod_cast hnat'
    dsimp only [U, V]
    linarith
  have hint : ∀ t, ∃ k : ℤ, V t - U t = (k:ℝ) := by
    rintro ⟨r, s⟩
    refine ⟨(n : ℤ) - (r.val : ℤ) - (s.val : ℤ), ?_⟩
    dsimp only [U, V]
    push_cast
    ring
  have hrange : ∀ t, w t ≠ 0 → |V t - U t| ≤ (n:ℝ) := by
    rintro ⟨r, s⟩ ht
    have hr : (r.val : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast (Nat.le_of_lt_succ r.isLt)
    have hs' : (s.val : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast (Nat.le_of_lt_succ s.isLt)
    have hrr : (0:ℝ) ≤ (r.val : ℝ) := Nat.cast_nonneg _
    have hss : (0:ℝ) ≤ (s.val : ℝ) := Nat.cast_nonneg _
    dsimp only [U, V]
    rw [abs_le]
    constructor <;> nlinarith
  have hcharge := finite_coupling_refined_charge w U V ((n:ℝ)/2) (1:ℝ)
    hw hprob hsame (by norm_num : (0:ℝ) ≤ 1) hstep
  have hmad : (∑ t, w t*|U t-(n:ℝ)/2|)=mad n := by
    rw [hU (fun z => |z-(n:ℝ)/2|),binomial_mad_eq]
  rw [hmad] at hcharge
  have hm := charge_mass_le w U V (n:ℝ) hw hprob hsame hstep hint
    (by exact_mod_cast hn) hrange
  have hq : (1:ℝ)^2*(∑ t, if 2/(3:ℝ) < V t - U t then w t else 0) ≤
      (n:ℝ)/((n:ℝ)+1) := by
    simpa only [one_pow, one_mul] using hm
  norm_num at hcharge hq
  calc
    _ = (2 : ℝ) ^ n * (∑ t, w t * (U t - V t) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [w, U, V, normalizedPairWeight]
      field_simp [binomialDenominator_ne_zero n]
      ring
    _ ≤ (2 : ℝ) ^ n * (4*mad n +
        (∑ t, if 2/(3:ℝ) < V t - U t then w t else 0)) :=
      mul_le_mul_of_nonneg_left hcharge (binomialDenominator_pos n).le
    _ ≤ (2 : ℝ) ^ n * (4*mad n + (n:ℝ)/((n:ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_left _ (binomialDenominator_pos n).le
      linarith [hq]
    _ = (4*mad n + (n:ℝ)/((n:ℝ)+1))*(2:ℝ)^n := by ring

/-- Spectral form of the d=1 charged block coupling. -/
theorem hsNormSq_centeredGrading_anticommutator_le_d1 {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 1 ≤ n) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - 1 → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*mad n + (n:ℝ)/((n:ℝ)+1))*(2:ℝ)^n := by
  rw [hsNormSq_centered_anticommutator hP H]
  apply block_coupling_refined_d1 n hn (fun r s => hsNormSq (P s * H * P r))
  · intro r s
    exact hsNormSq_nonneg _
  · intro r
    rw [sum_hsNormSq_blocks_column hP H r hleft, hmult]
  · intro s
    rw [sum_hsNormSq_blocks_row hP H s hright, hmult]
  · intro r s hrs
    rw [hvanish r s hrs, hsNormSq_zero]

/-- Trace-multiplicity form of the d=1 charged bound. -/
theorem hsNormSq_centeredGrading_anticommutator_le_of_trace_d1 {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 1 ≤ n) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - 1 → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*mad n + (n:ℝ)/((n:ℝ)+1))*(2:ℝ)^n := by
  apply hsNormSq_centeredGrading_anticommutator_le_d1 n hn P hP H hleft hright _ hvanish
  intro k
  rw [hsNormSq_projection (P k) (hP.conjTranspose_eq k) (hP.idempotent k), htrace]

/-- **Block instantiation of the finite-range compensated coupling** with
`a = d`, `L = n`, `m = n/2` — the uniform-in-`d` replacement of the `d = 1`
special-casing above, from `compensated_coupling_finite_range` (eq. (6)).

**The 4-vs-8 factor, resolved (R2125606741).** Substituting `a = d`, `L = n`
into eq. (6) yields the constant **4**: `4·d·mad n·(n+d)/(n+2d)`, and 4 is
correct at this level. The plan's **8** is not a coupling-level constant: the
paper's eq. (16) is `AS(f) ≤ 2·E(U−V)² ≤ 8·d·b_n·(n+d)/(n+2d)`, so the
factor 2 sits in the **edge comparison one level up** — not in Lemma 2 / eq.
(6), not in the anticommutator normalization (our
`hsNormSq_centered_anticommutator` already identifies the anticommutator's
HS norm with exactly this double sum), and not in the weighted filtration.
Source of the 2: the paper's §3 deficit bookkeeping — from (13),
`|E(h)|/4 ≤ A_h + 2A_0 ≤ 2(A_h + A_0)` while `‖T‖²_HS ≥ 4(A_h + A_0)`, hence
`|E(h)| ≤ 2‖T‖²_HS`. In our tree that doubling is already carried by
`edge_recovery` (`((orderedConstantEdges h).card : ℝ) ≤ 2 * hsNormSq (M*H+H*M)`,
OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean) feeding
`normalized_edge_bound`. So the AS(f)-level constant really is
`8·d·mad n·(n+d)/(n+2d) = 2 ×` this theorem's right-hand side — the plan's
sketch wrote the AS(f)-level number at the coupling step. Thread this at 4;
the 8 reappears at the edge comparison.

`hn : 1 ≤ n` supplies the range length `L = n > 0`. -/
theorem block_coupling_finite_range
    (n d : ℕ) (hn : 1 ≤ n) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        (4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)))*(2:ℝ)^n := by
  let w : Fin (n + 1) × Fin (n + 1) → ℝ :=
    normalizedPairWeight B ((2 : ℝ) ^ n)
  let U : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => (t.2.val : ℝ)
  let V : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun t => (n : ℝ) - (t.1.val : ℝ)
  have hU (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (U t)) =
        ∑ s : Fin (n + 1), binomialWeight n s * φ (s.val : ℝ) := by
    simpa only [w, U, hcol, binomialWeight] using
      normalizedPairWeight_expect_snd B ((2 : ℝ) ^ n)
        (fun s => φ (s.val : ℝ))
  have hV (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (V t)) =
        ∑ r : Fin (n + 1),
          binomialWeight n r * φ ((n : ℝ) - (r.val : ℝ)) := by
    simpa only [w, V, hrow, binomialWeight] using
      normalizedPairWeight_expect_fst B ((2 : ℝ) ^ n)
        (fun r => φ ((n : ℝ) - (r.val : ℝ)))
  have hw : ∀ t, 0 ≤ w t :=
    normalizedPairWeight_nonneg B _ hB (binomialDenominator_pos n).le
  have hsame : ∀ φ : ℝ → ℝ,
      (∑ t, w t * φ (U t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hU, hV, binomialWeight_reflect]
  have hstep : ∀ t, w t ≠ 0 → V t - U t ≤ (d : ℝ) := by
    rintro ⟨r, s⟩ ht
    have hnonzero : B r s ≠ 0 := by
      intro hz
      exact ht (by simp only [w, normalizedPairWeight, hz, zero_div])
    have hnat : n - d ≤ r.val + s.val :=
      Nat.le_of_not_gt (fun hlt => hnonzero (hvanish r s hlt))
    have hnat' : n ≤ r.val + s.val + d := by omega
    have hreal : (n : ℝ) ≤ (r.val : ℝ) + (s.val : ℝ) + (d : ℝ) := by
      exact_mod_cast hnat'
    dsimp only [U, V]
    linarith
  have hmad : (∑ t, w t*|U t-(n:ℝ)/2|)=mad n := by
    rw [hU (fun z => |z-(n:ℝ)/2|),binomial_mad_eq]
  -- `compensated_coupling_finite_range` wants its step/range bounds for EVERY
  -- index, but off the support of `w` (where `B r s = 0`) the raw `U` has
  -- `V t - U t = n - r - s > d` in general.  Repair `U` off the support by
  -- setting it equal to `V` there: every `w`-weighted sum is unchanged
  -- (zero terms vanish), and the pointwise bounds hold on the nose.
  let U' : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => if w t = 0 then V t else U t
  have hU'on : ∀ t, w t ≠ 0 → U' t = U t := by
    intro t ht
    dsimp only [U']
    rw [if_neg ht]
  have hU'off : ∀ t, w t = 0 → U' t = V t := by
    intro t ht
    dsimp only [U']
    rw [if_pos ht]
  have hsumU' (f : ℝ → ℝ) : (∑ t, w t * f (U' t)) = ∑ t, w t * f (U t) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases hw0 : w t = 0
    · rw [hw0, zero_mul, zero_mul]
    · rw [hU'on t hw0]
  have hsumsq : (∑ t, w t * (V t - U' t)^2) = ∑ t, w t * (V t - U t)^2 := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases hw0 : w t = 0
    · rw [hw0, zero_mul, zero_mul]
    · rw [hU'on t hw0]
  have hsame' : ∀ φ : ℝ → ℝ, (∑ t, w t * φ (U' t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hsumU' φ]
    exact hsame φ
  have hstep' : ∀ t, V t - U' t ≤ (d:ℝ) := by
    intro t
    by_cases hw0 : w t = 0
    · rw [hU'off t hw0]
      linarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d]
    · rw [hU'on t hw0]
      exact hstep t hw0
  have hrange' : ∀ t, U' t - V t ≤ (n:ℝ) := by
    rintro ⟨r, s⟩
    by_cases hw0 : w (r, s) = 0
    · rw [hU'off _ hw0]
      linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]
    · rw [hU'on _ hw0]
      have hr : (r.val : ℝ) ≤ (n:ℝ) := by
        exact_mod_cast (Nat.le_of_lt_succ r.isLt)
      have hs' : (s.val : ℝ) ≤ (n:ℝ) := by
        exact_mod_cast (Nat.le_of_lt_succ s.isLt)
      dsimp only [U, V]
      linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast (show 0 < n from by omega)
  have hfin := compensated_coupling_finite_range w U' V ((n:ℝ)/2) (d:ℝ) (n:ℝ)
    hw hsame' (Nat.cast_nonneg d) hstep' hnpos hrange'
  have hsumUabs' : (∑ t, w t * |U' t - (n:ℝ)/2|) = ∑ t, w t * |U t - (n:ℝ)/2| :=
    hsumU' (fun z => |z-(n:ℝ)/2|)
  rw [hsumsq, hsumUabs', hmad] at hfin
  have hbound : (∑ t, w t * (U t - V t)^2) ≤
      4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)) := by
    have hconv : (∑ t, w t * (U t - V t)^2) = ∑ t, w t * (V t - U t)^2 := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [hconv]
    exact hfin
  calc
    _ = (2 : ℝ) ^ n * (∑ t, w t * (U t - V t) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [w, U, V, normalizedPairWeight]
      field_simp [binomialDenominator_ne_zero n]
      ring
    _ ≤ (2 : ℝ) ^ n * (4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ))) :=
      mul_le_mul_of_nonneg_left hbound (binomialDenominator_pos n).le
    _ = (4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)))*(2:ℝ)^n := by ring

/-- Spectral form of the uniform finite block coupling. -/
theorem hsNormSq_centeredGrading_anticommutator_le_finite_range {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (hn : 1 ≤ n) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)))*(2:ℝ)^n := by
  rw [hsNormSq_centered_anticommutator hP H]
  apply block_coupling_finite_range n d hn (fun r s => hsNormSq (P s * H * P r))
  · intro r s
    exact hsNormSq_nonneg _
  · intro r
    rw [sum_hsNormSq_blocks_column hP H r hleft, hmult]
  · intro s
    rw [sum_hsNormSq_blocks_row hP H s hright, hmult]
  · intro r s hrs
    rw [hvanish r s hrs, hsNormSq_zero]

/-- Trace-multiplicity form of the uniform finite block coupling. -/
theorem hsNormSq_centeredGrading_anticommutator_le_of_trace_finite_range {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (hn : 1 ≤ n) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*(d:ℝ)*mad n*((n:ℝ)+(d:ℝ))/((n:ℝ)+2*(d:ℝ)))*(2:ℝ)^n := by
  apply hsNormSq_centeredGrading_anticommutator_le_finite_range n d hn P hP H
    hleft hright _ hvanish
  intro k
  rw [hsNormSq_projection (P k) (hP.conjTranspose_eq k) (hP.idempotent k), htrace]

end AverageSensitivity
