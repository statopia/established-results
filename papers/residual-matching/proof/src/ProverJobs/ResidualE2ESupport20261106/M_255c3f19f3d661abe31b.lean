import Lean
import ProverJobs.ResidualE2ESupport20261106.M_2899ebcb4b6cf51030cf
import ProverJobs.ResidualE2ESupport20261106.M_30e3ebd8c0ecef26f046

namespace PaperProofTasks.ResidualE2ESupport20261106

run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3684688107_efbf5172 : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Omega → ℝ)
    (hOm_meas : ∀ i j, Measurable (Om i j))
    (hOm_indep : ProbabilityTheory.iIndepFun (fun ij : Fin m × Fin n => Om ij.1 ij.2) P)
    (hOm_bin : ∀ i j, ∀ᵐ omega ∂P, Om i j omega = 0 ∨ Om i j omega = 1)
    (hOm_int : ∀ i j, MeasureTheory.Integrable (Om i j) P)
    (hOm_mean : ∀ i j, ∫ omega, Om i j omega ∂P = p)
    (a : Fin m → Fin n → ℝ),
    (∫ omega, (∑ i : Fin m, ∑ j : Fin n,
        a i j * ((Om i j omega - p) / Real.sqrt ((m : ℝ) * p)))^2 ∂P)
      = ((1 - p) / (m : ℝ)) * (∑ i : Fin m, ∑ j : Fin n, (a i j)^2) := by
  /- @proof-region region.target-node.session.9aee1074c08553e2 begin -/
  intro m n hm hn p hp0 hp1 Ω instΩ P instP Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean a
  set s : ℝ := Real.sqrt ((m : ℝ) * p) with hs_def
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmp : (0 : ℝ) < (m : ℝ) * p := mul_pos hmpos hp0
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos_of_pos hmp
  have hs2 : s ^ 2 = (m : ℝ) * p := by rw [hs_def]; exact Real.sq_sqrt hmp.le
  let ξ : Fin m × Fin n → Ω → ℝ := fun ij ω => (Om ij.1 ij.2 ω - p) / s

  let w : Fin m × Fin n → ℝ := fun ij => a ij.1 ij.2
  have hsum : ∀ ω : Ω, (∑ i : Fin m, ∑ j : Fin n, a i j * ((Om i j ω - p) / s))
      = ∑ p : Fin m × Fin n, w p * ξ p ω := by
    intro ω
    rw [Fintype.sum_prod_type]
  have hsumsq : (∑ i : Fin m, ∑ j : Fin n, (a i j) ^ 2)
      = ∑ p : Fin m × Fin n, (w p) ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [hsumsq]
  simp only [hsum]
  have hOm_bound : ∀ q : Fin m × Fin n, ∀ᵐ ω ∂P, ‖Om q.1 q.2 ω‖ ≤ 1 := by
    intro q
    filter_upwards [hOm_bin q.1 q.2] with ω hω
    rcases hω with h | h <;> rw [h] <;> simp
  have hOm_aesm : ∀ q : Fin m × Fin n, AEStronglyMeasurable (Om q.1 q.2) P :=
    fun q => (hOm_meas q.1 q.2).aestronglyMeasurable
  have hOmprod_int : ∀ u v : Fin m × Fin n, Integrable (fun ω => Om u.1 u.2 ω * Om v.1 v.2 ω) P := by
    intro u v
    refine MeasureTheory.Integrable.of_bound ((hOm_aesm u).mul (hOm_aesm v)) 1 ?_
    filter_upwards [hOm_bound u, hOm_bound v] with ω h1 h2
    rw [Real.norm_eq_abs] at h1 h2 ⊢
    rw [abs_mul]

    have h3 := mul_le_mul h1 h2 (abs_nonneg (Om v.1 v.2 ω)) (by norm_num : (0:ℝ) ≤ 1)
    linarith
  have hOm_sq : ∀ q : Fin m × Fin n, ∫ ω, Om q.1 q.2 ω * Om q.1 q.2 ω ∂P = p := by
    intro q
    have hae : (fun ω => Om q.1 q.2 ω * Om q.1 q.2 ω) =ᵐ[P] Om q.1 q.2 := by
      filter_upwards [hOm_bin q.1 q.2] with ω hω
      rcases hω with h | h <;> rw [h] <;> ring
    rw [MeasureTheory.integral_congr_ae hae, hOm_mean q.1 q.2]
  have hOm_cross : ∀ u v : Fin m × Fin n, u ≠ v →
      ∫ ω, Om u.1 u.2 ω * Om v.1 v.2 ω ∂P = p * p := by
    intro u v huv
    have hind : ProbabilityTheory.IndepFun (Om u.1 u.2) (Om v.1 v.2) P := hOm_indep.indepFun huv
    have h := ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hind (hOm_aesm u) (hOm_aesm v)
    rw [h, hOm_mean u.1 u.2, hOm_mean v.1 v.2]
  have hbound : ∀ q : Fin m × Fin n, ∀ᵐ ω ∂P, ‖ξ q ω‖ ≤ 1 / s := by
    intro q
    filter_upwards [hOm_bin q.1 q.2] with ω hω
    have h1 : |Om q.1 q.2 ω - p| ≤ 1 := by
      rcases hω with h | h
      · rw [h, zero_sub, abs_neg, abs_of_pos hp0]; linarith
      · rw [h, abs_of_nonneg (by linarith)]; linarith
    simp only [ξ]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.2 hs))

  have hξ_aesm : ∀ q : Fin m × Fin n, AEStronglyMeasurable (ξ q) P := by
    intro q
    simp only [ξ]
    exact (((hOm_meas q.1 q.2).sub measurable_const).div_const s).aestronglyMeasurable
  have hξ_int : ∀ q : Fin m × Fin n, Integrable (ξ q) P := by
    intro q
    exact MeasureTheory.Integrable.of_bound (hξ_aesm q) (1 / s) (hbound q)
  have hbound2 : ∀ pq : (Fin m × Fin n) × (Fin m × Fin n), ∀ᵐ ω ∂P,
      ‖ξ pq.1 ω * ξ pq.2 ω‖ ≤ (1 / s) * (1 / s) := by
    intro pq
    filter_upwards [hbound pq.1, hbound pq.2] with ω h1 h2
    rw [Real.norm_eq_abs, abs_mul]
    have h0 : (0:ℝ) ≤ 1 / s := le_of_lt (one_div_pos.2 hs)
    exact mul_le_mul h1 h2 (abs_nonneg (ξ pq.2 ω)) h0
  have hξξ_int : ∀ p q : Fin m × Fin n, Integrable (fun ω => ξ p ω * ξ q ω) P := by
    intro p q
    exact MeasureTheory.Integrable.of_bound ((hξ_aesm p).mul (hξ_aesm q))
      ((1 / s) * (1 / s)) (hbound2 (p, q))
  have hmean0 : ∀ u : Fin m × Fin n, ∫ ω, (Om u.1 u.2 ω - p) ∂P = 0 := by
    intro u
    rw [MeasureTheory.integral_sub (hOm_int u.1 u.2) (integrable_const p), hOm_mean u.1 u.2]
    simp
  have hcenter_cross : ∀ u v : Fin m × Fin n, u ≠ v →
      ∫ ω, (Om u.1 u.2 ω - p) * (Om v.1 v.2 ω - p) ∂P = 0 := by
    intro u v huv
    have hpt : ∀ ω : Ω, (Om u.1 u.2 ω - p) * (Om v.1 v.2 ω - p)
        = (Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
          - p * (Om v.1 v.2 ω - p) := by
      intro ω; ring
    have hi1 : Integrable (fun ω => Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) P :=
      (hOmprod_int u v).sub (integrable_const (p * p))
    have hi2 : Integrable (fun ω => p * (Om u.1 u.2 ω - p)) P :=
      ((hOm_int u.1 u.2).sub (integrable_const p)).const_mul p
    have hi3 : Integrable (fun ω => p * (Om v.1 v.2 ω - p)) P :=
      ((hOm_int v.1 v.2).sub (integrable_const p)).const_mul p
    have h1 : ∫ ω, (Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) ∂P = p * p - p * p := by
      rw [MeasureTheory.integral_sub (hOmprod_int u v) (integrable_const (p * p)),
        hOm_cross u v huv]
      simp
    have h2 : ∫ ω, p * (Om u.1 u.2 ω - p) ∂P = 0 := by
      rw [MeasureTheory.integral_const_mul, hmean0 u, mul_zero]
    have h3 : ∫ ω, p * (Om v.1 v.2 ω - p) ∂P = 0 := by
      rw [MeasureTheory.integral_const_mul, hmean0 v, mul_zero]
    have e1 : ∫ ω, ((Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) - p * (Om u.1 u.2 ω - p)) ∂P
        = (∫ ω, (Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) ∂P)
          - ∫ ω, p * (Om u.1 u.2 ω - p) ∂P :=
      MeasureTheory.integral_sub hi1 hi2
    have hi12 : Integrable (fun ω => (Om u.1 u.2 ω * Om v.1 v.2 ω - p * p)
        - p * (Om u.1 u.2 ω - p)) P :=
      hi1.sub hi2
    have e2 : ∫ ω, ((Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
          - p * (Om v.1 v.2 ω - p)) ∂P
        = (∫ ω, ((Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) - p * (Om u.1 u.2 ω - p)) ∂P)
          - ∫ ω, p * (Om v.1 v.2 ω - p) ∂P :=
      MeasureTheory.integral_sub hi12 hi3
    calc ∫ ω, (Om u.1 u.2 ω - p) * (Om v.1 v.2 ω - p) ∂P
        = ∫ ω, ((Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
            - p * (Om v.1 v.2 ω - p)) ∂P := by
          rw [show (fun ω => (Om u.1 u.2 ω - p) * (Om v.1 v.2 ω - p))
                = (fun ω => (Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
                    - p * (Om v.1 v.2 ω - p)) from funext hpt]
      _ = ((∫ ω, (Om u.1 u.2 ω * Om v.1 v.2 ω - p * p) ∂P)
            - ∫ ω, p * (Om u.1 u.2 ω - p) ∂P) - ∫ ω, p * (Om v.1 v.2 ω - p) ∂P := by
          rw [e2, e1]
      _ = 0 := by rw [h1, h2, h3]; ring
  have hcenter_diag : ∀ u : Fin m × Fin n,
      ∫ ω, (Om u.1 u.2 ω - p) * (Om u.1 u.2 ω - p) ∂P = p - p * p := by
    intro u
    have hpt : ∀ ω : Ω, (Om u.1 u.2 ω - p) * (Om u.1 u.2 ω - p)
        = (Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
          - p * (Om u.1 u.2 ω - p) := by
      intro ω; ring
    have hi1 : Integrable (fun ω => Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) P :=
      (hOmprod_int u u).sub (integrable_const (p * p))
    have hi2 : Integrable (fun ω => p * (Om u.1 u.2 ω - p)) P :=
      ((hOm_int u.1 u.2).sub (integrable_const p)).const_mul p
    have h1 : ∫ ω, (Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) ∂P = p - p * p := by
      rw [MeasureTheory.integral_sub (hOmprod_int u u) (integrable_const (p * p)), hOm_sq u]
      simp
    have h2 : ∫ ω, p * (Om u.1 u.2 ω - p) ∂P = 0 := by
      rw [MeasureTheory.integral_const_mul, hmean0 u, mul_zero]
    have e1 : ∫ ω, ((Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) - p * (Om u.1 u.2 ω - p)) ∂P
        = (∫ ω, (Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) ∂P)
          - ∫ ω, p * (Om u.1 u.2 ω - p) ∂P :=
      MeasureTheory.integral_sub hi1 hi2
    have hi12 : Integrable (fun ω => (Om u.1 u.2 ω * Om u.1 u.2 ω - p * p)
        - p * (Om u.1 u.2 ω - p)) P :=
      hi1.sub hi2
    have e2 : ∫ ω, ((Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
          - p * (Om u.1 u.2 ω - p)) ∂P
        = (∫ ω, ((Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) - p * (Om u.1 u.2 ω - p)) ∂P)
          - ∫ ω, p * (Om u.1 u.2 ω - p) ∂P :=
      MeasureTheory.integral_sub hi12 hi2
    calc ∫ ω, (Om u.1 u.2 ω - p) * (Om u.1 u.2 ω - p) ∂P
        = ∫ ω, ((Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
            - p * (Om u.1 u.2 ω - p)) ∂P := by
          rw [show (fun ω => (Om u.1 u.2 ω - p) * (Om u.1 u.2 ω - p))
                = (fun ω => (Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) - p * (Om u.1 u.2 ω - p)
                    - p * (Om u.1 u.2 ω - p)) from funext hpt]
      _ = ((∫ ω, (Om u.1 u.2 ω * Om u.1 u.2 ω - p * p) ∂P)
            - ∫ ω, p * (Om u.1 u.2 ω - p) ∂P) - ∫ ω, p * (Om u.1 u.2 ω - p) ∂P := by
          rw [e2, e1]
      _ = p - p * p := by rw [h1, h2]; ring
  have hξ_cross : ∀ u v : Fin m × Fin n, u ≠ v → ∫ ω, ξ u ω * ξ v ω ∂P = 0 := by
    intro u v huv
    have hpt : ∀ ω : Ω, ξ u ω * ξ v ω
        = ((Om u.1 u.2 ω - p) * (Om v.1 v.2 ω - p)) / (s * s) := by
      intro ω
      simp only [ξ]
      rw [div_mul_div_comm]
    have hstep : ∫ ω, ξ u ω * ξ v ω ∂P
        = (∫ ω, (Om u.1 u.2 ω - p) * (Om v.1 v.2 ω - p) ∂P) * (s * s)⁻¹ := by
      rw [show (fun ω => ξ u ω * ξ v ω)
            = (fun ω => ((Om u.1 u.2 ω - p) * (Om v.1 v.2 ω - p)) / (s * s))
            from funext hpt]
      simp only [div_eq_mul_inv, MeasureTheory.integral_mul_const]
    rw [hstep, hcenter_cross u v huv, zero_mul]
  have hξ_diag : ∀ u : Fin m × Fin n, ∫ ω, ξ u ω * ξ u ω ∂P = (1 - p) / (m : ℝ) := by
    intro u
    have hpt : ∀ ω : Ω, ξ u ω * ξ u ω
        = ((Om u.1 u.2 ω - p) * (Om u.1 u.2 ω - p)) / (s * s) := by
      intro ω
      simp only [ξ]
      rw [div_mul_div_comm]
    have hstep : ∫ ω, ξ u ω * ξ u ω ∂P
        = (∫ ω, (Om u.1 u.2 ω - p) * (Om u.1 u.2 ω - p) ∂P) * (s * s)⁻¹ := by
      rw [show (fun ω => ξ u ω * ξ u ω)
            = (fun ω => ((Om u.1 u.2 ω - p) * (Om u.1 u.2 ω - p)) / (s * s))
            from funext hpt]
      simp only [div_eq_mul_inv, MeasureTheory.integral_mul_const]
    rw [hstep, hcenter_diag u]
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have hpne : p ≠ 0 := ne_of_gt hp0
    have hss : s * s = (m : ℝ) * p := by rw [← sq, hs2]
    have hden : (m : ℝ) * p ≠ 0 := mul_ne_zero hmne hpne
    rw [hss, div_eq_mul_inv]
    field_simp

  have hexp : ∀ ω : Ω, (∑ u : Fin m × Fin n, w u * ξ u ω) ^ 2
      = ∑ u, ∑ v, w u * w v * (ξ u ω * ξ v ω) := by
    intro ω
    rw [sq, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hInt0 : ∫ ω, (∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
        w pq.1 * w pq.2 * (ξ pq.1 ω * ξ pq.2 ω)) ∂P
      = ∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
          ∫ ω, w pq.1 * w pq.2 * (ξ pq.1 ω * ξ pq.2 ω) ∂P := by
    exact MeasureTheory.integral_finset_sum Finset.univ
      (f := fun (pq : (Fin m × Fin n) × (Fin m × Fin n)) (ω : Ω) =>
        w pq.1 * w pq.2 * (ξ pq.1 ω * ξ pq.2 ω))
      (fun (pq : (Fin m × Fin n) × (Fin m × Fin n)) _ =>
        (hξξ_int pq.1 pq.2).const_mul (w pq.1 * w pq.2))
  have hInt1 : (∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
        ∫ ω, w pq.1 * w pq.2 * (ξ pq.1 ω * ξ pq.2 ω) ∂P)
      = ∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
          w pq.1 * w pq.2 * (∫ ω, ξ pq.1 ω * ξ pq.2 ω ∂P) := by
    refine Finset.sum_congr rfl (fun pq _ => ?_)
    exact MeasureTheory.integral_const_mul (w pq.1 * w pq.2)
      (fun ω => ξ pq.1 ω * ξ pq.2 ω)
  have hback : (∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
        w pq.1 * w pq.2 * (∫ ω, ξ pq.1 ω * ξ pq.2 ω ∂P))
      = ∑ u, ∑ v, w u * w v * (∫ ω, ξ u ω * ξ v ω ∂P) := by
    rw [Fintype.sum_prod_type]
  have hdiag : (∑ u : Fin m × Fin n, ∑ v, w u * w v * (∫ ω, ξ u ω * ξ v ω ∂P))
      = ∑ u, w u * w u * ((1 - p) / (m : ℝ)) := by
    apply Finset.sum_congr rfl
    intro u _
    have hf : ∀ v, v ≠ u → w u * w v * (∫ ω, ξ u ω * ξ v ω ∂P) = 0 := by
      intro v hv
      rw [hξ_cross u v (Ne.symm hv), mul_zero]
    have hsub : (∑ x ∈ ({u} : Finset (Fin m × Fin n)),
          w u * w x * (∫ ω, ξ u ω * ξ x ω ∂P))
        = ∑ x, w u * w x * (∫ ω, ξ u ω * ξ x ω ∂P) := by
      refine Finset.sum_subset (Finset.singleton_subset_iff.2 (Finset.mem_univ u)) ?_
      intro x _ hx
      exact hf x (by simpa using hx)
    rw [← hsub]
    simp [hξ_diag u]

  have hfinal : (∑ u : Fin m × Fin n, w u * w u * ((1 - p) / (m : ℝ)))
      = ((1 - p) / (m : ℝ)) * ∑ u, (w u) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hmain : ∫ ω, (∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
        w pq.1 * w pq.2 * (ξ pq.1 ω * ξ pq.2 ω)) ∂P
      = ∑ u, w u * w u * ((1 - p) / (m : ℝ)) := by
    rw [hInt0, hInt1, hback, hdiag]
  have hflatten : (fun ω : Ω => ∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
        w pq.1 * w pq.2 * (ξ pq.1 ω * ξ pq.2 ω))
      = (fun ω => ∑ u : Fin m × Fin n, ∑ v, w u * w v * (ξ u ω * ξ v ω)) := by
    funext ω
    rw [Fintype.sum_prod_type]
  have hstart : ∫ ω, (∑ u : Fin m × Fin n, w u * ξ u ω) ^ 2 ∂P
      = ∫ ω, (∑ pq : (Fin m × Fin n) × (Fin m × Fin n),
          w pq.1 * w pq.2 * (ξ pq.1 ω * ξ pq.2 ω)) ∂P := by
    rw [show (fun ω => (∑ u : Fin m × Fin n, w u * ξ u ω) ^ 2)
          = (fun ω => ∑ u, ∑ v, w u * w v * (ξ u ω * ξ v ω)) from funext hexp]
    rw [← hflatten]
  rw [hstart, hmain, hfinal]





  /- @proof-region region.target-node.session.9aee1074c08553e2 end -/

end

end Statlib.Imported

