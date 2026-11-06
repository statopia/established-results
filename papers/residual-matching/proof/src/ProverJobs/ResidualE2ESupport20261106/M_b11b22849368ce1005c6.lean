import Statlib.StatFoundation.Concentration.ExponentialType.mcdiarmid_meas_ge_le_exp
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_18127a92ee88073b370e
import ProverJobs.ResidualE2ESupport20261106.M_6ea1d0aa8e53e4855480
import ProverJobs.ResidualE2ESupport20261106.M_24e4399710401de9771f

namespace PaperProofTasks.ResidualE2ESupport20261106



open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_3073978187_c577ca52 : ∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ)
    (x : ℝ) (u : ℝ) (hu : 0 < u),
    μ {ω : Ω | u ≤
        |(n : ℝ)⁻¹ * ((Finset.univ.filter (fun j : Fin n =>
              svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ)
          - (∫ ω, (n : ℝ)⁻¹ * ((Finset.univ.filter (fun j : Fin n =>
              svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) ∂μ)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * u ^ 2 / 2)) := by
  /- @proof-region region.target-node.session.5a1a2127d3262a6c begin -/
  refine fun m n hm hn hnm p hp0 hp1 {Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] => ?_
  intro Xi Mask hXi_meas hMask_meas hXi_indep hMask_indep hIndep x u hu
  classical
  set CX : Fin n → Ω → ((Fin m → ℝ) × (Fin m → ℝ)) :=
    fun j ω => (fun i => Xi ω i j, fun i => Mask ω i j) with hCX
  set G : Ω → ℝ := fun ω => ((n : ℝ))⁻¹ * ((Finset.univ.filter (fun j : Fin n =>
      svals (maskedScaled p (Xi ω) (Mask ω)) j ≤ x)).card : ℝ) with hG
  set f : (Fin n → ((Fin m → ℝ) × (Fin m → ℝ))) → ℝ := fun c =>
    ((n : ℝ))⁻¹ * ((Finset.univ.filter (fun j : Fin n =>
      svals (maskedScaled p (fun i j' => (c j').1 i) (fun i j' => (c j').2 i)) j ≤ x)).card : ℝ) with hf
  have hconv : (μ {ω : Ω | u ≤ |G ω - ∫ ω, G ω ∂μ|})
      = μ {ω : Ω | u ≤ |f (fun j => CX j ω) - ∫ ω, f (fun j => CX j ω) ∂μ|} := rfl
  rw [hconv]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  set c : Fin n → ℝ := fun _ => 2 / (n : ℝ) with hc
  have hterm : ∀ i : Fin n, c i ^ 2 = (2 / (n : ℝ)) ^ 2 := fun i => by rw [hc]
  have hcS : (∑ i : Fin n, c i ^ 2) = 4 / (n : ℝ) := by
    calc (∑ i : Fin n, c i ^ 2) = ∑ i : Fin n, (2 / (n : ℝ)) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (n : ℝ) * (2 / (n : ℝ)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 4 / (n : ℝ) := by
            field_simp
            ring
  have hcpos : 0 < ∑ i : Fin n, c i ^ 2 := by
    rw [hcS]
    exact div_pos (by norm_num) hnpos
  have hmeasC : ∀ i : Fin n, Measurable (CX i) := by
    intro i
    have h1 : Measurable (fun ω : Ω => (fun k => Xi ω k i)) :=
      measurable_pi_iff.mpr (fun k => hXi_meas k i)
    have h2 : Measurable (fun ω : Ω => (fun k => Mask ω k i)) :=
      measurable_pi_iff.mpr (fun k => hMask_meas k i)
    exact Measurable.prodMk h1 h2
  have hindC : iIndepFun CX μ :=
    statopia_math_node_527567249_0af0d987 m n μ Xi Mask hXi_meas hMask_meas hXi_indep hMask_indep
      hIndep
  have hmeaf : Measurable f := by
    set g : (Fin n → ((Fin m → ℝ) × (Fin m → ℝ))) → Matrix (Fin m) (Fin n) ℝ :=
      fun c => maskedScaled p (fun i j' => (c j').1 i) (fun i j' => (c j').2 i) with hgdef
    have hX : ∀ (i : Fin m) (j : Fin n),
        Measurable (fun c : Fin n → ((Fin m → ℝ) × (Fin m → ℝ)) => (c j).1 i) := by
      intro i j
      exact (measurable_pi_apply i).comp (measurable_fst.comp (measurable_pi_apply j))
    have hM : ∀ (i : Fin m) (j : Fin n),
        Measurable (fun c : Fin n → ((Fin m → ℝ) × (Fin m → ℝ)) => (c j).2 i) := by
      intro i j
      exact (measurable_pi_apply i).comp (measurable_snd.comp (measurable_pi_apply j))
    have hgentry : ∀ (i : Fin m) (j : Fin n), Measurable (fun c => g c i j) := by
      intro i j
      simp only [hgdef, maskedScaled, div_eq_mul_inv]
      exact Measurable.mul (Measurable.mul (hM i j) (hX i j)) measurable_const
    have hΦ : Measurable (fun c => fun j : Fin n => svals (g c) j) := by
      refine measurable_pi_iff.mpr (fun j => ?_)
      exact statopia_math_node_760072556_5eef0e48 m n g hgentry j
    have hstep : Measurable (fun t : ℝ => if t ≤ x then ((n : ℝ))⁻¹ else 0) :=
      Measurable.ite measurableSet_Iic measurable_const measurable_const
    have hcount : Measurable
        (fun y : Fin n → ℝ => ∑ j : Fin n, (if y j ≤ x then ((n : ℝ))⁻¹ else 0)) := by
      refine Finset.measurable_sum _ (fun j _ => ?_)
      exact hstep.comp (measurable_pi_apply j)
    have hH : (fun y : Fin n → ℝ =>
          ((n : ℝ))⁻¹ * ((Finset.univ.filter (fun j : Fin n => y j ≤ x)).card : ℝ))
        = fun y : Fin n → ℝ => ∑ j : Fin n, (if y j ≤ x then ((n : ℝ))⁻¹ else 0) := by
      funext y
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : y j ≤ x <;> simp [h]
    have hfeq : f = (fun y : Fin n → ℝ =>
        ∑ j : Fin n, (if y j ≤ x then ((n : ℝ))⁻¹ else 0)) ∘ (fun c => fun j => svals (g c) j) := by
      funext c
      exact congrFun hH (fun j => svals (g c) j)
    rw [hfeq]
    exact hcount.comp hΦ
  have hbd : ∀ (i : Fin n) (a b : (Fin m → ℝ) × (Fin m → ℝ))
        (cs : Fin n → ((Fin m → ℝ) × (Fin m → ℝ))),
      |f (Function.update cs i a) - f (Function.update cs i b)| ≤ c i := by
    intro i a b cs
    have hcol : ∀ j : Fin n, j ≠ i → Function.update cs i b j = Function.update cs i a j := by
      intro j hj
      simp [hj]
    set A : Matrix (Fin m) (Fin n) ℝ :=
      maskedScaled p (fun r j => (Function.update cs i a j).1 r)
        (fun r j => (Function.update cs i a j).2 r) with hA
    set B : Matrix (Fin m) (Fin n) ℝ :=
      maskedScaled p (fun r j => (Function.update cs i b j).1 r)
        (fun r j => (Function.update cs i b j).2 r) with hB
    have hBA : ∀ (r : Fin m) (j : Fin n), j ≠ i → B r j = A r j := by
      intro r j hj
      have hj' := hcol j hj
      simp only [hA, hB, maskedScaled]
      rw [hj']
    have hkey := statopia_math_node_3763049950_70a2cee1 m n A B i x hBA
    have hfA : f (Function.update cs i a)
        = ((n : ℝ))⁻¹ * (↑(Finset.univ.filter (fun j : Fin n => svals A j ≤ x)).card) := by
      simp only [hf, hA]
    have hfB : f (Function.update cs i b)
        = ((n : ℝ))⁻¹ * (↑(Finset.univ.filter (fun j : Fin n => svals B j ≤ x)).card) := by
      simp only [hf, hB]
    rw [hfA, hfB]
    have hfac : ((n : ℝ))⁻¹ * (↑(Finset.univ.filter (fun j : Fin n => svals A j ≤ x)).card)
          - ((n : ℝ))⁻¹ * (↑(Finset.univ.filter (fun j : Fin n => svals B j ≤ x)).card)
        = ((n : ℝ))⁻¹ * ((↑(Finset.univ.filter (fun j : Fin n => svals A j ≤ x)).card)
          - (↑(Finset.univ.filter (fun j : Fin n => svals B j ≤ x)).card)) := by ring
    rw [hfac, abs_mul, abs_of_pos (inv_pos.mpr hnpos)]
    refine le_trans (mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr hnpos))) ?_
    simp only [hc]
    rw [div_eq_inv_mul]
  have hbdneg : ∀ (i : Fin n) (a b : (Fin m → ℝ) × (Fin m → ℝ))
        (cs : Fin n → ((Fin m → ℝ) × (Fin m → ℝ))),
      |(fun cs => - f cs) (Function.update cs i a) - (fun cs => - f cs) (Function.update cs i b)| ≤ c i := by
    intro i a b cs
    have h := hbd i a b cs
    have h2 : -f (Function.update cs i a) - -f (Function.update cs i b)
        = -(f (Function.update cs i a) - f (Function.update cs i b)) := by ring
    simpa only [Pi.neg_apply, h2, abs_neg] using h
  have hmeafneg : Measurable (fun cs : Fin n → ((Fin m → ℝ) × (Fin m → ℝ)) => -f cs) := hmeaf.neg
  have h1 := Statlib.StatFoundation.Concentration.ExponentialType.mcdiarmid_meas_ge_le_exp
    μ n CX f c u hindC hmeasC hmeaf hbd hu hcpos
  have h2 := Statlib.StatFoundation.Concentration.ExponentialType.mcdiarmid_meas_ge_le_exp
    μ n CX (fun cs => -f cs) c u hindC hmeasC hmeafneg hbdneg hu hcpos
  rw [hcS] at h1 h2
  have hexp : Real.exp (-2 * u ^ 2 / (4 / (n : ℝ))) = Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
    congr 1
    field_simp
    ring
  rw [hexp] at h1 h2
  have hsub : {ω : Ω | u ≤ |f (fun i => CX i ω) - ∫ ω', f (fun i => CX i ω') ∂μ|} ⊆
      {ω : Ω | u ≤ f (fun i => CX i ω) - ∫ ω', f (fun i => CX i ω') ∂μ} ∪
      {ω : Ω | u ≤ (fun cs => - f cs) (fun i => CX i ω)
        - ∫ ω', (fun cs => - f cs) (fun i => CX i ω') ∂μ} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases le_total 0 (f (fun i => CX i ω) - ∫ ω', f (fun i => CX i ω') ∂μ) with h0 | h0
    · left
      rw [abs_of_nonneg h0] at hω
      exact hω
    · right
      have hI : (∫ ω', -f (fun i => CX i ω') ∂μ) = -(∫ ω', f (fun i => CX i ω') ∂μ) :=
        integral_neg (f := fun ω' => f (fun i => CX i ω'))
      rw [abs_of_nonpos h0] at hω
      show u ≤ -f (fun i => CX i ω) - ∫ ω', -f (fun i => CX i ω') ∂μ
      rw [hI]
      linarith
  have hstep : (μ {ω : Ω | u ≤ |f (fun i => CX i ω) - ∫ ω', f (fun i => CX i ω') ∂μ|})
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * u ^ 2 / 2))
        + ENNReal.ofReal (Real.exp (-(n : ℝ) * u ^ 2 / 2)) := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add h1 h2
  have hsum : ENNReal.ofReal (Real.exp (-(n : ℝ) * u ^ 2 / 2))
        + ENNReal.ofReal (Real.exp (-(n : ℝ) * u ^ 2 / 2))
      = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * u ^ 2 / 2)) := by
    rw [← ENNReal.ofReal_add (le_of_lt (Real.exp_pos (-(n : ℝ) * u ^ 2 / 2)))
      (le_of_lt (Real.exp_pos (-(n : ℝ) * u ^ 2 / 2))), two_mul]
  exact hstep.trans (le_of_eq hsum)
  /- @proof-region region.target-node.session.5a1a2127d3262a6c end -/

end Statlib.Imported

