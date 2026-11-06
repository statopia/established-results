import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.WedinSinTheta
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_2162631172_eb3a62ea : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ),
    ‖A‖ = sSup {r : ℝ | ∃ x : Fin m → ℝ, ∃ y : Fin n → ℝ,
      (∑ i : Fin m, (x i) ^ 2 = 1) ∧ (∑ j : Fin n, (y j) ^ 2 = 1) ∧
        r = ∑ i : Fin m, ∑ j : Fin n, x i * A i j * y j} := by
  /- @proof-region region.target-node.session.03bec0ca494f564d begin -/
  intro m n hm hn A
  rw [← Statlib.HighDim.MatrixAnalysis.opNorm_eq_l2 A]
  unfold Statlib.HighDim.MatrixAnalysis.opNorm
  set T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) with hT
  set S : Set ℝ := {r : ℝ | ∃ x : Fin m → ℝ, ∃ y : Fin n → ℝ,
      (∑ i : Fin m, (x i) ^ 2 = 1) ∧ (∑ j : Fin n, (y j) ^ 2 = 1) ∧
        r = ∑ i : Fin m, ∑ j : Fin n, x i * A i j * y j} with hS
  have hTact : ∀ v : EuclideanSpace ℝ (Fin n), (T v).ofLp = A.mulVec v.ofLp := by
    intro v
    rw [hT]
    exact Matrix.ofLp_toEuclideanLin_apply A v
  have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := by
    intro a b
    simp [mul_comm]
  have hmv : ∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin m),
      (A.mulVec v.ofLp) i = ∑ j : Fin n, A i j * v.ofLp j := fun v i => rfl
  have hinner : ∀ (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)),
      inner ℝ u (T v) = ∑ i : Fin m, ∑ j : Fin n, u.ofLp i * A i j * v.ofLp j := by
    intro u v
    rw [PiLp.inner_apply]
    simp only [hreal, hTact v, hmv v, Finset.mul_sum, mul_assoc]
  have hnsq_m : ∀ u : EuclideanSpace ℝ (Fin m), ‖u‖ ^ 2 = ∑ i, (u.ofLp i) ^ 2 := by
    intro u
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hnsq_n : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ^ 2 = ∑ j, (v.ofLp j) ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hcoe_m : ∀ x : Fin m → ℝ, (∑ i, (x i) ^ 2 = 1) →
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ = 1 := by
    intro x hx
    have hsq : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ ^ 2 = 1 := by
      rw [hnsq_m]
      simpa using hx
    nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))]
  have hcoe_n : ∀ y : Fin n → ℝ, (∑ j, (y j) ^ 2 = 1) →
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    intro y hy
    have hsq : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      rw [hnsq_n]
      simpa using hy
    nlinarith [norm_nonneg (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))]
  have hle' : ∀ (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)),
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u (T v) ≤ ‖T‖ := by
    intro u v hu hv
    calc inner ℝ u (T v) ≤ ‖u‖ * ‖T v‖ := real_inner_le_norm u (T v)
      _ = ‖T v‖ := by rw [hu, one_mul]
      _ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ = ‖T‖ := by rw [hv, mul_one]
  have hmem_le : ∀ r ∈ S, r ≤ ‖T‖ := by
    intro r hr
    rw [hS] at hr
    obtain ⟨x, y, hx, hy, rfl⟩ := hr
    have h1 := hle' (WithLp.toLp 2 x) (WithLp.toLp 2 y) (hcoe_m x hx) (hcoe_n y hy)
    rw [hinner] at h1
    simpa using h1
  have hbdd : BddAbove S := ⟨‖T‖, hmem_le⟩
  have hA : sSup S ≤ ‖T‖ := Real.sSup_le hmem_le (norm_nonneg T)
  have hex_m : ∃ x : Fin m → ℝ, ∑ i, (x i) ^ 2 = 1 := by
    refine ⟨fun i => if i = (⟨0, hm⟩ : Fin m) then (1 : ℝ) else 0, ?_⟩
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hex_n : ∃ y : Fin n → ℝ, ∑ j, (y j) ^ 2 = 1 := by
    refine ⟨fun j => if j = (⟨0, hn⟩ : Fin n) then (1 : ℝ) else 0, ?_⟩
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨x0, hx0⟩ := hex_m
  obtain ⟨y0, hy0⟩ := hex_n
  have h0 : (0 : ℝ) ≤ sSup S := by
    have hmem0 : (∑ i : Fin m, ∑ j : Fin n, x0 i * A i j * y0 j) ∈ S := by
      rw [hS]
      exact ⟨x0, y0, hx0, hy0, rfl⟩
    have hmem0' : (-(∑ i : Fin m, ∑ j : Fin n, x0 i * A i j * y0 j)) ∈ S := by
      rw [hS]
      have hsqu : (∑ i : Fin m, (-x0 i) ^ 2) = 1 := by
        have : (∑ i : Fin m, (-x0 i) ^ 2) = ∑ i : Fin m, (x0 i) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        rw [this, hx0]
      have hneg : (∑ i : Fin m, ∑ j : Fin n, (-x0 i) * A i j * y0 j)
          = -(∑ i : Fin m, ∑ j : Fin n, x0 i * A i j * y0 j) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      exact ⟨fun i => -x0 i, y0, hsqu, hy0, hneg.symm⟩
    have h1 := le_csSup hbdd hmem0
    have h2 := le_csSup hbdd hmem0'
    linarith
  have hstep : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ‖T v‖ ≤ sSup S := by
    intro v hv
    by_cases hTv : T v = 0
    · rw [hTv, norm_zero]
      exact h0
    · have hne : ‖T v‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact hTv
      have h2v : (∑ j : Fin n, (v.ofLp j) ^ 2) = 1 := by
        have h := hnsq_n v
        rw [hv] at h
        simpa using h.symm
      have hunit_x : (∑ i : Fin m, (‖T v‖⁻¹ * (T v).ofLp i) ^ 2) = 1 := by
        have hstep1 : (∑ i : Fin m, (‖T v‖⁻¹ * (T v).ofLp i) ^ 2)
            = ‖T v‖⁻¹ ^ 2 * (∑ i : Fin m, ((T v).ofLp i) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_pow]
        rw [hstep1, ← hnsq_m (T v), inv_pow]
        refine inv_mul_cancel₀ ?_
        rw [pow_two]
        exact mul_ne_zero hne hne
      have hval : (∑ i : Fin m, ∑ j : Fin n, (‖T v‖⁻¹ * (T v).ofLp i) * A i j * (v.ofLp j))
          = ‖T v‖ := by
        have hfac : (∑ i : Fin m, ∑ j : Fin n, (‖T v‖⁻¹ * (T v).ofLp i) * A i j * (v.ofLp j))
            = ‖T v‖⁻¹ * (∑ i : Fin m, ∑ j : Fin n, (T v).ofLp i * A i j * (v.ofLp j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [mul_assoc]
        rw [hfac, ← hinner (T v) v, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
          inv_mul_cancel₀ hne, one_mul]
      refine le_csSup hbdd ?_
      rw [hS]
      exact ⟨fun i => ‖T v‖⁻¹ * (T v).ofLp i, v.ofLp, hunit_x, h2v, hval.symm⟩
  have hB : ‖T‖ ≤ sSup S := by
    refine ContinuousLinearMap.opNorm_le_bound T h0 (fun v => ?_)
    by_cases hv : ‖v‖ = 0
    · have hv0 : v = 0 := norm_eq_zero.mp hv
      simp [hv0]
    · have hv1 : ‖(‖v‖⁻¹ • v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
          inv_mul_cancel₀ hv]
      have hb := hstep (‖v‖⁻¹ • v) hv1
      have hkey : ‖T (‖v‖⁻¹ • v)‖ * ‖v‖ = ‖T v‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
          mul_comm (‖v‖⁻¹) (‖T v‖), mul_assoc, inv_mul_cancel₀ hv, mul_one]
      rw [← hkey]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg v)
  exact le_antisymm hB hA
  /- @proof-region region.target-node.session.03bec0ca494f564d end -/

end Statlib.Imported

