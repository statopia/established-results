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
theorem statopia_math_node_3069358588_912211ca : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Ωm : Type*} [MeasurableSpace Ωm]
    (P : Measure Ωm) [IsProbabilityMeasure P]
    (Om : Fin m → Fin n → Ωm → ℝ)
    (hOm_meas : ∀ i j, Measurable (Om i j))
    (hOm_indep : ProbabilityTheory.iIndepFun
      (fun ij : Fin m × Fin n => Om ij.1 ij.2) P)
    (hOm_bin : ∀ i j, ∀ᵐ ω ∂P, Om i j ω = 0 ∨ Om i j ω = 1)
    (hOm_int : ∀ i j, MeasureTheory.Integrable (Om i j) P)
    (hOm_mean : ∀ i j, ∫ ω, Om i j ω ∂P = p),
    (Matrix.of (fun i k => ∫ ω, ∑ j : Fin n,
        ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) *
          ((Om k j ω - p) / Real.sqrt ((m : ℝ) * p)) ∂P)
      = ((n : ℝ) * (1 - p) / (m : ℝ)) • (1 : Matrix (Fin m) (Fin m) ℝ)) ∧
    (Matrix.of (fun j l => ∫ ω, ∑ i : Fin m,
        ((Om i j ω - p) / Real.sqrt ((m : ℝ) * p)) *
          ((Om i l ω - p) / Real.sqrt ((m : ℝ) * p)) ∂P)
      = (1 - p) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  /- @proof-region region.target-node.session.d558793229cc1c4c begin -/
  intro m n hm hn hnm p hp0 hp1 Ωm hΩm P hP Om hOm_meas hOm_indep hOm_bin hOm_int hOm_mean
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hmul : (0 : ℝ) < (m : ℝ) * p := mul_pos hmpos hp0
  have hmulne : ((m : ℝ) * p) ≠ 0 := mul_ne_zero hmne hpne
  set s := Real.sqrt ((m : ℝ) * p) with hs
  have hspos : 0 < s := by
    rw [hs]
    exact Real.sqrt_pos.2 hmul
  have hssq : s ^ 2 = (m : ℝ) * p := by
    rw [hs]
    exact Real.sq_sqrt hmul.le
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hconst : ∀ c : ℝ, ∫ _ : Ωm, c ∂P = c := by
    intro c
    simp
  have hbd : ∀ a : Fin m × Fin n, ∀ᵐ ω ∂P, |Om a.1 a.2 ω - p| ≤ 1 := by
    intro a
    filter_upwards [hOm_bin a.1 a.2] with ω h
    rw [abs_le]
    rcases h with h | h <;> rw [h] <;> constructor <;> linarith
  have hZmean : ∀ a : Fin m × Fin n, ∫ ω, (Om a.1 a.2 ω - p) ∂P = 0 := by
    intro a
    rw [MeasureTheory.integral_sub (hOm_int a.1 a.2) (MeasureTheory.integrable_const p),
      hOm_mean a.1 a.2, hconst p]
    ring
  have hZsq : ∀ a : Fin m × Fin n, ∫ ω, (Om a.1 a.2 ω - p) ^ 2 ∂P = p - p ^ 2 := by
    intro a
    have hfun : (fun ω => (Om a.1 a.2 ω - p) ^ 2)
        =ᵐ[P] (fun ω => (1 - 2 * p) * Om a.1 a.2 ω + p ^ 2) := by
      filter_upwards [hOm_bin a.1 a.2] with ω h
      rcases h with h | h <;> rw [h] <;> ring
    rw [MeasureTheory.integral_congr_ae hfun,
      MeasureTheory.integral_add ((hOm_int a.1 a.2).const_mul (1 - 2 * p))
        (MeasureTheory.integrable_const (p ^ 2)),
      MeasureTheory.integral_const_mul, hOm_mean a.1 a.2, hconst (p ^ 2)]
    ring
  have hpair : ∀ a b : Fin m × Fin n,
      ∫ ω, (Om a.1 a.2 ω - p) * (Om b.1 b.2 ω - p) ∂P
        = if a = b then p - p ^ 2 else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      have hfun : (fun ω => (Om a.1 a.2 ω - p) * (Om a.1 a.2 ω - p))
          = (fun ω => (Om a.1 a.2 ω - p) ^ 2) := by
        funext ω
        ring
      rw [hfun]
      exact hZsq a
    · rw [if_neg hab]
      have hcomp : ∫ ω, (Om a.1 a.2 ω - p) * (Om b.1 b.2 ω - p) ∂P
          = (∫ ω, (Om a.1 a.2 ω - p) ∂P) * (∫ ω, (Om b.1 b.2 ω - p) ∂P) :=
        ProbabilityTheory.IndepFun.integral_fun_comp_mul_comp
          (μ := P) (X := Om a.1 a.2) (Y := Om b.1 b.2)
          (f := fun x : ℝ => x - p) (g := fun y : ℝ => y - p)
          (hOm_indep.indepFun (i := a) (j := b) hab)
          (hOm_meas a.1 a.2).aemeasurable (hOm_meas b.1 b.2).aemeasurable
          (measurable_id.sub measurable_const).aestronglyMeasurable
          (measurable_id.sub measurable_const).aestronglyMeasurable
      rw [hcomp, hZmean a, hZmean b, mul_zero]
  have hs2inv : s⁻¹ * s⁻¹ = ((m : ℝ) * p)⁻¹ := by
    rw [← mul_inv, ← pow_two, hssq]
  have hval : s⁻¹ * s⁻¹ * (p - p ^ 2) = (1 - p) / (m : ℝ) := by
    rw [hs2inv]
    field_simp
    try ring
  have harith1 : (n : ℝ) * (s⁻¹ * s⁻¹ * (p - p ^ 2)) = (n : ℝ) * ((1 - p) / (m : ℝ)) := by
    rw [hval]
  have harith2 : (m : ℝ) * (s⁻¹ * s⁻¹ * (p - p ^ 2)) = 1 - p := by
    rw [hval]
    field_simp
    try ring
  have hprod_int2 : ∀ a b : Fin m × Fin n,
      MeasureTheory.Integrable
        (fun ω => ((Om a.1 a.2 ω - p) / s) * ((Om b.1 b.2 ω - p) / s)) P := by
    intro a b
    have hm1 : Measurable (fun ω => (Om a.1 a.2 ω - p) / s) :=
      ((hOm_meas a.1 a.2).sub measurable_const).div_const s
    have hm2 : Measurable (fun ω => (Om b.1 b.2 ω - p) / s) :=
      ((hOm_meas b.1 b.2).sub measurable_const).div_const s
    refine MeasureTheory.Integrable.of_bound (hm1.mul hm2).aestronglyMeasurable (s⁻¹ * s⁻¹) ?_
    filter_upwards [hbd a, hbd b] with ω h1 h2
    rw [Real.norm_eq_abs, abs_mul]
    have hb1 : |(Om a.1 a.2 ω - p) / s| ≤ s⁻¹ := by
      rw [abs_div, abs_of_pos hspos, div_eq_mul_inv]
      have hnn : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.2 hspos.le
      have h' := mul_le_mul_of_nonneg_right h1 hnn
      simpa using h'
    have hb2 : |(Om b.1 b.2 ω - p) / s| ≤ s⁻¹ := by
      rw [abs_div, abs_of_pos hspos, div_eq_mul_inv]
      have hnn : (0 : ℝ) ≤ s⁻¹ := inv_nonneg.2 hspos.le
      have h' := mul_le_mul_of_nonneg_right h2 hnn
      simpa using h'
    exact mul_le_mul hb1 hb2 (abs_nonneg _) (inv_nonneg.2 hspos.le)
  have hscaled2 : ∀ a b : Fin m × Fin n,
      ∫ ω, ((Om a.1 a.2 ω - p) / s) * ((Om b.1 b.2 ω - p) / s) ∂P
        = s⁻¹ * s⁻¹ * (if a = b then p - p ^ 2 else 0) := by
    intro a b
    have hfun : (fun ω => ((Om a.1 a.2 ω - p) / s) * ((Om b.1 b.2 ω - p) / s))
        = (fun ω => s⁻¹ * (s⁻¹ * ((Om a.1 a.2 ω - p) * (Om b.1 b.2 ω - p)))) := by
      funext ω
      rw [div_eq_inv_mul, div_eq_inv_mul]
      ring
    rw [hfun, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hpair a b]
    ring
  have entry1 : ∀ i k : Fin m,
      ∫ ω, ∑ j : Fin n, ((Om i j ω - p) / s) * ((Om k j ω - p) / s) ∂P
        = if i = k then (n : ℝ) * ((1 - p) / (m : ℝ)) else 0 := by
    intro i k
    have hsum : ∫ ω, ∑ j : Fin n, ((Om i j ω - p) / s) * ((Om k j ω - p) / s) ∂P
        = ∑ j : Fin n, ∫ ω, ((Om i j ω - p) / s) * ((Om k j ω - p) / s) ∂P := by
      simpa using (MeasureTheory.integral_finset_sum (Finset.univ)
        (f := fun j ω => ((Om i j ω - p) / s) * ((Om k j ω - p) / s))
        (fun j _ => hprod_int2 (i, j) (k, j)))
    rw [hsum]
    by_cases hik : i = k
    · rw [if_pos hik]
      have hterm : ∀ j : Fin n,
          ∫ ω, ((Om i j ω - p) / s) * ((Om k j ω - p) / s) ∂P
            = s⁻¹ * s⁻¹ * (p - p ^ 2) := by
        intro j
        rw [hscaled2 (i, j) (k, j), if_pos (by rw [hik])]
      calc ∑ j : Fin n, ∫ ω, ((Om i j ω - p) / s) * ((Om k j ω - p) / s) ∂P
          = ∑ j : Fin n, s⁻¹ * s⁻¹ * (p - p ^ 2) := Finset.sum_congr rfl (fun j _ => hterm j)
        _ = (n : ℝ) * (s⁻¹ * s⁻¹ * (p - p ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (n : ℝ) * ((1 - p) / (m : ℝ)) := harith1
    · rw [if_neg hik]
      have hterm : ∀ j : Fin n,
          ∫ ω, ((Om i j ω - p) / s) * ((Om k j ω - p) / s) ∂P = 0 := by
        intro j
        rw [hscaled2 (i, j) (k, j),
          if_neg (fun h => hik (by simpa using congrArg Prod.fst h))]
        ring
      calc ∑ j : Fin n, ∫ ω, ((Om i j ω - p) / s) * ((Om k j ω - p) / s) ∂P
          = ∑ j : Fin n, (0 : ℝ) := Finset.sum_congr rfl (fun j _ => hterm j)
        _ = 0 := by simp
  have entry2 : ∀ j l : Fin n,
      ∫ ω, ∑ i : Fin m, ((Om i j ω - p) / s) * ((Om i l ω - p) / s) ∂P
        = if j = l then (1 - p) else 0 := by
    intro j l
    have hsum : ∫ ω, ∑ i : Fin m, ((Om i j ω - p) / s) * ((Om i l ω - p) / s) ∂P
        = ∑ i : Fin m, ∫ ω, ((Om i j ω - p) / s) * ((Om i l ω - p) / s) ∂P := by
      simpa using (MeasureTheory.integral_finset_sum (Finset.univ)
        (f := fun i ω => ((Om i j ω - p) / s) * ((Om i l ω - p) / s))
        (fun i _ => hprod_int2 (i, j) (i, l)))
    rw [hsum]
    by_cases hjl : j = l
    · rw [if_pos hjl]
      have hterm : ∀ i : Fin m,
          ∫ ω, ((Om i j ω - p) / s) * ((Om i l ω - p) / s) ∂P
            = s⁻¹ * s⁻¹ * (p - p ^ 2) := by
        intro i
        rw [hscaled2 (i, j) (i, l), if_pos (by rw [hjl])]
      calc ∑ i : Fin m, ∫ ω, ((Om i j ω - p) / s) * ((Om i l ω - p) / s) ∂P
          = ∑ i : Fin m, s⁻¹ * s⁻¹ * (p - p ^ 2) := Finset.sum_congr rfl (fun i _ => hterm i)
        _ = (m : ℝ) * (s⁻¹ * s⁻¹ * (p - p ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = 1 - p := harith2
    · rw [if_neg hjl]
      have hterm : ∀ i : Fin m,
          ∫ ω, ((Om i j ω - p) / s) * ((Om i l ω - p) / s) ∂P = 0 := by
        intro i
        rw [hscaled2 (i, j) (i, l),
          if_neg (fun h => hjl (by simpa using congrArg Prod.snd h))]
        ring
      calc ∑ i : Fin m, ∫ ω, ((Om i j ω - p) / s) * ((Om i l ω - p) / s) ∂P
          = ∑ i : Fin m, (0 : ℝ) := Finset.sum_congr rfl (fun i _ => hterm i)
        _ = 0 := by simp
  constructor
  · ext i k
    rw [Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, entry1 i k]
    by_cases hik : i = k
    · simp [hik]
      ring_nf
    · simp [hik]
  · ext j l
    rw [Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, entry2 j l]
    by_cases hjl : j = l <;> simp [hjl]
  /- @proof-region region.target-node.session.d558793229cc1c4c end -/

end

end Statlib.Imported

