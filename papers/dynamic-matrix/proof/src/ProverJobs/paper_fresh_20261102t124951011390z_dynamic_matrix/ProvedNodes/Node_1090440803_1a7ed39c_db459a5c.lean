import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Vocabulary
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.Base
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ProvedNodes.Node_1013838252_0af447c5_513bc185
import ProverJobs.paper_fresh_20261102t124951011390z_dynamic_matrix.ExternalNodes.Node_400580fcfedf4b228464

namespace PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix


open MeasureTheory
open _root_.PaperProofTasks.paper_fresh_20261102t124951011390z_dynamic_matrix.Statlib.Imported

open MeasureTheory
namespace Statlib.Imported

variable {Ω : Type*} [MeasurableSpace Ω]

set_option autoImplicit false in
theorem statopia_math_node_1090440803_1a7ed39c : ∀ (m1 m2 : ℕ)
    (Sigma : Matrix (Fin m1 × Fin m2) (Fin m1 × Fin m2) ℝ) (hSigma : Sigma.PosDef)
    (mu kappa : ℝ)
    (hmu : mu = lamMin hSigma.isHermitian.eigenvalues)
    (hmu_pos : 0 < mu)
    (hkappa : kappa = lamMax hSigma.isHermitian.eigenvalues / mu)
    (H D : Matrix (Fin m1) (Fin m2) ℝ),
    mu * (frobNorm H ^ 2 - kappa * frobNorm D * frobNorm H) ≤
      (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf H a * Sigma a b * vecOf H b) +
        (∑ a : Fin m1 × Fin m2, ∑ b : Fin m1 × Fin m2,
          vecOf D a * Sigma a b * vecOf H b) := by
  /- @proof-region region.target-node.session.880541b1109b395d begin -/
  intro m1 m2 Sigma hSigma mu kappa hmu hmu_pos hkappa H D
  have hA : Sigma.IsHermitian := hSigma.isHermitian
  have hSymm : ∀ a b : Fin m1 × Fin m2, Sigma a b = Sigma b a := by
    intro a b
    simpa using Matrix.IsHermitian.apply hA b a
  have p5 : ∀ j : Fin m1 × Fin m2,
      Sigma.mulVec (hA.eigenvectorBasis j).ofLp = hA.eigenvalues j • (hA.eigenvectorBasis j).ofLp := by
    intro j
    exact hA.mulVec_eigenvectorBasis j
  have p6 : ∀ v : Fin m1 × Fin m2 → ℝ, (WithLp.toLp 2 v).ofLp = v := by
    intro v
    simp
  have p2 : ∀ i j : Fin m1 × Fin m2,
      inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    exact orthonormal_iff_ite.1 hA.eigenvectorBasis.orthonormal i j
  have p3 : ∀ V : EuclideanSpace ℝ (Fin m1 × Fin m2),
      ∑ i, (hA.eigenvectorBasis.repr V).ofLp i • hA.eigenvectorBasis i = V := by
    intro V
    exact OrthonormalBasis.sum_repr hA.eigenvectorBasis V
  have q1 : ∀ x y : EuclideanSpace ℝ (Fin m1 × Fin m2), inner ℝ x y = y.ofLp ⬝ᵥ x.ofLp := by
    intro x y
    exact EuclideanSpace.inner_eq_star_dotProduct x y
  have q2 : ∀ (V : EuclideanSpace ℝ (Fin m1 × Fin m2)) (j : Fin m1 × Fin m2),
      (hA.eigenvectorBasis.repr V).ofLp j = inner ℝ (hA.eigenvectorBasis j) V := by
    intro V j
    exact OrthonormalBasis.repr_apply_apply hA.eigenvectorBasis V j
  have h_exp : ∀ V : EuclideanSpace ℝ (Fin m1 × Fin m2),
      ∑ j, inner ℝ (hA.eigenvectorBasis j) V • hA.eigenvectorBasis j = V := by
    intro V
    conv_rhs => rw [← p3 V]
    exact Finset.sum_congr rfl (fun j _ => by rw [q2 V j])
  have h_bilin : ∀ (p q : Fin m1 × Fin m2 → ℝ),
      inner ℝ (∑ i, p i • hA.eigenvectorBasis i) (∑ j, q j • hA.eigenvectorBasis j)
        = ∑ i, p i * q i := by
    intro p q
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, p2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · simp
      exact mul_comm (q i) (p i)
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have d2 : ∀ (v w : Fin m1 × Fin m2 → ℝ), v ⬝ᵥ w = ∑ a, v a * w a := by
    intro v w
    rfl
  have h_mv_apply : ∀ (v : Fin m1 × Fin m2 → ℝ) (a : Fin m1 × Fin m2),
      (Sigma.mulVec v) a = ∑ b, Sigma a b * v b := by
    intro v a
    rfl
  have d1 : ∀ (v w : Fin m1 × Fin m2 → ℝ) (r : ℝ), v ⬝ᵥ (r • w) = r * (v ⬝ᵥ w) := by
    intro v w r
    rw [d2, d2, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hs : (r • w) a = r * w a := rfl
    rw [hs]
    ring
  have h_adj : ∀ v w : Fin m1 × Fin m2 → ℝ,
      (Sigma.mulVec v) ⬝ᵥ w = v ⬝ᵥ (Sigma.mulVec w) := by
    intro v w
    have e1 : (Sigma.mulVec v) ⬝ᵥ w = ∑ a, ∑ b, Sigma a b * v b * w a := by
      rw [d2]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [h_mv_apply, Finset.sum_mul]
    have e2 : v ⬝ᵥ (Sigma.mulVec w) = ∑ a, ∑ b, v a * (Sigma a b * w b) := by
      rw [d2]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [h_mv_apply, Finset.mul_sum]
    rw [e1, e2]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hSymm y x]
    ring
  have step1 : ∀ (u v : Fin m1 × Fin m2 → ℝ), (∑ a, u a * (Sigma.mulVec v) a)
      = inner ℝ (WithLp.toLp 2 (Sigma.mulVec v)) (WithLp.toLp 2 u) := by
    intro u v
    rw [q1, p6, d2]
  have step2 : ∀ (X Y : EuclideanSpace ℝ (Fin m1 × Fin m2)),
      inner ℝ X Y
        = ∑ j, inner ℝ (hA.eigenvectorBasis j) X * inner ℝ (hA.eigenvectorBasis j) Y := by
    intro X Y
    conv_lhs => rw [← h_exp X]
    conv_lhs => rw [← h_exp Y]
    rw [h_bilin]
  have step3 : ∀ (v : Fin m1 × Fin m2 → ℝ) (j : Fin m1 × Fin m2),
      inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 (Sigma.mulVec v))
        = hA.eigenvalues j * inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 v) := by
    intro v j
    simp only [q1, p6]
    rw [h_adj v, p5 j, d1]
  have h_cross : ∀ (u v : Fin m1 × Fin m2 → ℝ),
      (∑ a, u a * (Sigma.mulVec v) a)
        = ∑ j, hA.eigenvalues j
            * inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 u)
            * inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 v) := by
    intro u v
    rw [step1 u v, step2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [step3 v j]
    ring
  have h_diag : ∀ v : Fin m1 × Fin m2 → ℝ,
      (∑ a, v a * (Sigma.mulVec v) a)
        = ∑ j, hA.eigenvalues j
            * (inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 v)) ^ 2 := by
    intro v
    rw [h_cross v v]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h_par : ∀ v : Fin m1 × Fin m2 → ℝ,
      (∑ a, v a ^ 2)
        = ∑ j, (inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 v)) ^ 2 := by
    intro v
    have h2 : (∑ a, v a * v a) = inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
      rw [q1, p6, d2]
    have h1 : (∑ a, v a ^ 2) = ∑ a, v a * v a :=
      Finset.sum_congr rfl (fun a _ => by ring)
    rw [h1, h2, step2]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hlo : ∀ j : Fin m1 × Fin m2, (⨅ i, hA.eigenvalues i) ≤ hA.eigenvalues j := by
    intro j
    exact ciInf_le (Set.finite_range hA.eigenvalues).bddBelow j
  have hhi : ∀ j : Fin m1 × Fin m2, hA.eigenvalues j ≤ (⨆ i, hA.eigenvalues i) := by
    intro j
    exact le_ciSup (f := hA.eigenvalues) (Set.finite_range hA.eigenvalues).bddAbove j
  have hmu_id : mu = (⨅ i, hA.eigenvalues i) := hmu
  have hkap_id : kappa = (⨆ i, hA.eigenvalues i) / mu := hkappa
  have hmunu : mu * kappa = (⨆ i, hA.eigenvalues i) := by
    rw [hkap_id, mul_comm]
    exact div_mul_cancel₀ _ (ne_of_gt hmu_pos)
  rcases Nat.eq_zero_or_pos m1 with h1 | h1
  · subst m1
    simp [frobNorm]
  rcases Nat.eq_zero_or_pos m2 with h2 | h2
  · subst m2
    simp [frobNorm]
  haveI hne : Nonempty (Fin m1 × Fin m2) := ⟨(⟨0, h1⟩, ⟨0, h2⟩)⟩
  have he_pos : ∀ j : Fin m1 × Fin m2, 0 < hA.eigenvalues j := by
    intro j
    have h := hlo j
    rw [← hmu_id] at h
    linarith
  have hnu_nn : 0 ≤ (⨆ i, hA.eigenvalues i) := by
    have h := hhi (⟨0, h1⟩, ⟨0, h2⟩)
    have h2' := he_pos (⟨0, h1⟩, ⟨0, h2⟩)
    linarith
  have habs_sq : ∀ x : Fin m1 × Fin m2 → ℝ,
      (∑ j, |x j| ^ 2) = ∑ j, x j ^ 2 := by
    intro x
    exact Finset.sum_congr rfl (fun j _ => by simp)
  have h_cauchy : ∀ (x y : Fin m1 × Fin m2 → ℝ),
      (∑ j, |x j| * |y j|)
        ≤ Real.sqrt (∑ j, x j ^ 2) * Real.sqrt (∑ j, y j ^ 2) := by
    intro x y
    have hsq : (∑ j, |x j| * |y j|) ^ 2 ≤ (∑ j, x j ^ 2) * ∑ j, y j ^ 2 := by
      have h3 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) (fun j => |x j|) (fun j => |y j|)
      rw [habs_sq x, habs_sq y] at h3
      simpa using h3
    have hnn : 0 ≤ ∑ j, |x j| * |y j| :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hnn2 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hnn3 : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h4 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hnn, Real.sqrt_mul hnn2] at h4
    exact h4
  have h_cross_abs : ∀ (x y : Fin m1 × Fin m2 → ℝ),
      -((⨆ i, hA.eigenvalues i)
          * (Real.sqrt (∑ j, x j ^ 2) * Real.sqrt (∑ j, y j ^ 2)))
        ≤ ∑ j, hA.eigenvalues j * x j * y j := by
    intro x y
    have h1' : -(∑ j, |hA.eigenvalues j * x j * y j|)
        ≤ ∑ j, hA.eigenvalues j * x j * y j := by
      have hsum : (∑ j, -( |hA.eigenvalues j * x j * y j| ))
          ≤ ∑ j, hA.eigenvalues j * x j * y j :=
        Finset.sum_le_sum (fun j _ => (abs_le.1 (le_refl (|hA.eigenvalues j * x j * y j|))).1)
      simpa using hsum
    have h2' : (∑ j, |hA.eigenvalues j * x j * y j|)
        = ∑ j, hA.eigenvalues j * |x j| * |y j| := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [abs_mul, abs_mul, abs_of_pos (he_pos j)]
    have h3' : (∑ j, hA.eigenvalues j * |x j| * |y j|)
        ≤ (⨆ i, hA.eigenvalues i) * ∑ j, |x j| * |y j| := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hhi j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h4' : (⨆ i, hA.eigenvalues i) * ∑ j, |x j| * |y j|
        ≤ (⨆ i, hA.eigenvalues i) * (Real.sqrt (∑ j, x j ^ 2) * Real.sqrt (∑ j, y j ^ 2)) :=
      mul_le_mul_of_nonneg_left (h_cauchy x y) hnu_nn
    linarith
  have h_low : mu * (∑ a : Fin m1 × Fin m2, vecOf H a ^ 2)
      ≤ ∑ a : Fin m1 × Fin m2, vecOf H a * (Sigma.mulVec (vecOf H)) a := by
    rw [h_diag (vecOf H), h_par (vecOf H), hmu_id, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hlo j) (sq_nonneg _))
  have h_cr : -((⨆ i, hA.eigenvalues i)
        * (Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf D a ^ 2)
          * Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf H a ^ 2)))
      ≤ ∑ a : Fin m1 × Fin m2, vecOf D a * (Sigma.mulVec (vecOf H)) a := by
    rw [h_cross (vecOf D) (vecOf H)]
    have hb := h_cross_abs
      (fun j => inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 (vecOf D)))
      (fun j => inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 (vecOf H)))
    rw [← h_par (vecOf D), ← h_par (vecOf H)] at hb
    exact hb
  obtain ⟨-, -, -, -, -, -, hVec, hNorm, -, -⟩ :=
    statopia_math_node_1013838252_0af447c5 m1 m2 Sigma hSigma
  have hsqrtH : Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf H a ^ 2) ^ 2
      = ∑ a : Fin m1 × Fin m2, vecOf H a ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg (vecOf H a)))
  have hring : mu * ((∑ a : Fin m1 × Fin m2, vecOf H a ^ 2)
        - kappa * Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf D a ^ 2)
          * Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf H a ^ 2))
      = mu * (∑ a : Fin m1 × Fin m2, vecOf H a ^ 2)
        - (mu * kappa)
          * (Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf D a ^ 2)
            * Real.sqrt (∑ a : Fin m1 × Fin m2, vecOf H a ^ 2)) := by
    ring
  rw [hVec H H, hVec D H, ← hNorm H, ← hNorm D, hsqrtH, hring, hmunu]
  linarith [h_low, h_cr]
  /- @proof-region region.target-node.session.880541b1109b395d end -/

end Statlib.Imported

