import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_065aa1069a714115f680
import ProverJobs.ResidualE2ESupport20261106.M_af528081b8600b9af0ba
import ProverJobs.ResidualE2ESupport20261106.M_bc006dd73253e8b4462a
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
theorem statopia_math_node_2592890691_3a10a58c : ∀ (D0 : ℝ) (hD0 : 0 < D0) (Kt : ℝ) (hKt : 0 < Kt)
    (alpha0 : ℝ) (hAlpha0 : 15 < alpha0)
    (rhoMinus : ℝ) (hRhoMinusPos : 0 < rhoMinus) (hRhoMinusLe : rhoMinus ≤ 1)
    (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hsparse : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
    (hrho_lo : rhoMinus ≤ (n : ℝ) / (m : ℝ)) (hrho_hi : (n : ℝ) / (m : ℝ) ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xi Mask : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hXi_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Xi ω i j)
    (hXi_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Xi ω i j) μ)
    (hXi_sq_int : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => (Xi ω i j) ^ 2) μ)
    (hXi_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Xi ω ij.1 ij.2) μ)
    (hXi_mean : ∀ (i : Fin m) (j : Fin n), ∫ ω, Xi ω i j ∂μ = 0)
    (hXi_var : ∀ (i : Fin m) (j : Fin n), ∫ ω, (Xi ω i j) ^ 2 ∂μ = 1)
    (hXi_tail : ∀ (i : Fin m) (j : Fin n) (t : ℝ), 0 < t →
      μ {ω | t < |Xi ω i j|} ≤ ENNReal.ofReal (2 * Real.exp (-t / Kt)))
    (hMask_meas : ∀ (i : Fin m) (j : Fin n), Measurable fun ω => Mask ω i j)
    (hMask_val : ∀ (i : Fin m) (j : Fin n) (ω : Ω), Mask ω i j = 0 ∨ Mask ω i j = 1)
    (hMask_law : ∀ (i : Fin m) (j : Fin n), μ {ω | Mask ω i j = 1} = ENNReal.ofReal p)
    (hMask_indep : iIndepFun (fun (ij : Fin m × Fin n) (ω : Ω) => Mask ω ij.1 ij.2) μ)
    (hIndep : IndepFun (fun ω (ij : Fin m × Fin n) => Xi ω ij.1 ij.2)
      (fun ω (ij : Fin m × Fin n) => Mask ω ij.1 ij.2) μ)
    
    
    
    (hbad : μ {ω : Ω | 4 < (⨆ i : Fin n, svals (maskedScaled p (Xi ω) (Mask ω)) i)}
      ≤ ENNReal.ofReal (Real.rpow (n : ℝ) (-(D0 + 2))))
    (hvanish : ∀ ω : Ω, (⨆ i : Fin n, svals (maskedScaled p (Xi ω) (Mask ω)) i) ≤ 4 →
      ∀ i : Fin n, svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ 4)
    (nuA nuRho : Measure ℝ)
    (hnuA_cdf : ∀ x : ℝ, (nuA (Set.Iic x)).toReal =
      ∫ ω, (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n =>
            svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n =>
            -(svals (maskedScaled p (Xi ω) (Mask ω)) i) ≤ x)).card : ℝ)) ∂μ)
    (hnuRho_cdf : ∀ x : ℝ, (nuRho (Set.Iic x)).toReal =
      ∫ u in Set.Iic x,
        (rootedMPDensity ((n : ℝ) / (m : ℝ)) u + rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2)
    (hmass : ∫ u in (mpLambdaMinus ((n : ℝ) / (m : ℝ)))..(mpLambdaPlus ((n : ℝ) / (m : ℝ))),
        rootedMPDensity ((n : ℝ) / (m : ℝ)) u = 1),
    MeasureTheory.IntegrableOn
        (fun x : ℝ => |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|)
        {x : ℝ | 4 < |x|}
      ∧ (∫ x in {x : ℝ | 4 < |x|},
          |(nuA (Set.Iic x)).toReal - (nuRho (Set.Iic x)).toReal|)
        ≤ Real.rpow (n : ℝ) (-(D0 + 2) / 2) := by
  /- @proof-region region.target-node.session.07ec289ce396e95d begin -/
  intro D0 hD0 Kt hKt alpha0 hAlpha0 rhoMinus hRhoMinusPos hRhoMinusLe m n hn hnm p hp0 hp1
    hsparse hrho_lo hrho_hi Ω hmΩ μ hμ Xi Mask hXi_meas hXi_int hXi_sq_int hXi_indep hXi_mean
    hXi_var hXi_tail hMask_meas hMask_val hMask_law hMask_indep hIndep hbad hvanish nuA nuRho
    hnuA_cdf hnuRho_cdf hmass
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have h : (0 : ℕ) < m := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn hnm)
    exact_mod_cast h
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := lt_of_lt_of_le Nat.zero_lt_one hn
    exact_mod_cast h
  have hρ0 : (0 : ℝ) < (n : ℝ) / (m : ℝ) := div_pos hn0 hm0
  have hρ1 : (n : ℝ) / (m : ℝ) ≤ 1 := hrho_hi
  have hsqrt_le : Real.sqrt ((n : ℝ) / (m : ℝ)) ≤ 1 := by
    nlinarith [Real.sq_sqrt hρ0.le, Real.sqrt_nonneg ((n : ℝ) / (m : ℝ)), hρ1]
  have hlamMinus_nonneg : 0 ≤ mpLambdaMinus ((n : ℝ) / (m : ℝ)) := by
    simp only [mpLambdaMinus]
    linarith
  have hlamPlus_le : mpLambdaPlus ((n : ℝ) / (m : ℝ)) ≤ 2 := by
    simp only [mpLambdaPlus]
    linarith
  have hsvals_nonneg : ∀ (ω : Ω) (i : Fin n),
      0 ≤ svals (maskedScaled p (Xi ω) (Mask ω)) i := by
    intro ω i
    simp only [svals]
    exact Real.sqrt_nonneg _
  classical
  let S : Ω → Fin n → ℝ := fun ω i => svals (maskedScaled p (Xi ω) (Mask ω)) i
  let Tr : Ω → ℝ := fun ω => ∑ i : Fin n, (S ω i) ^ 2
  let Ev : Set Ω := ⋃ i : Fin n, {ω | 4 < S ω i}
  let eps : ℝ := Real.rpow (n : ℝ) (-(D0 + 2))
  have heps_pos : 0 < eps := by
    simp only [eps]
    exact Real.rpow_pos_of_pos hn0 _
  have hS_nonneg : ∀ (ω : Ω) (i : Fin n), 0 ≤ S ω i := by
    intro ω i
    simpa only [S] using hsvals_nonneg ω i
  have hSvanish : ∀ (ω : Ω), (⨆ i : Fin n, S ω i) ≤ 4 → ∀ i : Fin n, S ω i ≤ 4 := by
    intro ω h i
    exact hvanish ω (by simpa only [S] using h) i
  have hEv : μ Ev ≤ ENNReal.ofReal eps := by
    have hsub : Ev ⊆ {ω : Ω | 4 < ⨆ i : Fin n, S ω i} := by
      intro ω hω
      simp only [Ev, Set.mem_iUnion, Set.mem_setOf_eq] at hω ⊢
      by_contra hcon
      push_neg at hcon
      obtain ⟨i, hi⟩ := hω
      linarith [hSvanish ω hcon i, hi]
    have hbads : μ {ω : Ω | 4 < ⨆ i : Fin n, S ω i} ≤ ENNReal.ofReal eps := by
      simpa only [S, eps] using hbad
    exact le_trans (measure_mono hsub) hbads
  have hEv_real : μ.real Ev ≤ eps := by
    have h1 : (μ Ev).toReal ≤ (ENNReal.ofReal eps).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hEv
    rwa [ENNReal.toReal_ofReal heps_pos.le] at h1
  have hFR_hi : ∀ x : ℝ, 4 ≤ x → (nuRho (Set.Iic x)).toReal = 1 :=
    statopia_math_node_1012033153_fe69c14e ((n : ℝ) / (m : ℝ)) hρ0 hρ1 nuRho hnuRho_cdf hmass
  have hFR_lo : ∀ x : ℝ, x ≤ -4 → (nuRho (Set.Iic x)).toReal = 0 := by
    intro x hx
    rw [hnuRho_cdf x]
    have hzero : ∀ u : ℝ, u ≤ x →
        (rootedMPDensity ((n : ℝ) / (m : ℝ)) u
            + rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2 = 0 := by
      intro u hu
      have hu' : u ≤ -4 := le_trans hu hx
      have h1 : rootedMPDensity ((n : ℝ) / (m : ℝ)) u = 0 := by
        simp only [rootedMPDensity]
        rw [if_neg]
        · exact mul_zero _
        · intro hcon
          linarith [hlamMinus_nonneg, hcon.1, hu']
      have h2 : rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u) = 0 := by
        simp only [rootedMPDensity]
        rw [if_neg]
        · exact mul_zero _
        · intro hcon
          linarith [hlamPlus_le, hcon.2, hu']
      rw [h1, h2]
      norm_num
    have hcongr : ∫ u in Set.Iic x,
          (rootedMPDensity ((n : ℝ) / (m : ℝ)) u
            + rootedMPDensity ((n : ℝ) / (m : ℝ)) (-u)) / 2 = ∫ u in Set.Iic x, (0 : ℝ) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro u hu
      exact hzero u hu
    rw [hcongr]
    simp
  have hSmeas : ∀ i : Fin n, Measurable fun ω => S ω i := by
    intro i
    have hg : ∀ (k : Fin m) (l : Fin n), Measurable fun ω =>
        maskedScaled p (Xi ω) (Mask ω) k l := by
      intro k l
      simp only [maskedScaled]
      exact ((hMask_meas k l).mul (hXi_meas k l)).div measurable_const
    have hmain := statopia_math_node_760072556_5eef0e48 (m := m) (n := n)
      (g := fun ω => maskedScaled p (Xi ω) (Mask ω)) hg i
    simpa only [S] using hmain
  have hFA_hi : ∀ x : ℝ, 0 ≤ x →
      1 - (nuA (Set.Iic x)).toReal =
        ∫ ω, (2 * (n : ℝ))⁻¹ *
          ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ := by
    intro x hx
    have hcdf : (nuA (Set.Iic x)).toReal =
        ∫ ω, (2 * (n : ℝ))⁻¹ *
          (((Finset.univ.filter (fun i : Fin n => S ω i ≤ x)).card : ℝ) +
            ((Finset.univ.filter (fun i : Fin n => -S ω i ≤ x)).card : ℝ)) ∂μ := by
      simpa only [S] using hnuA_cdf x
    rw [hcdf]
    have hcnt_meas : Measurable fun ω : Ω =>
        ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) := by
      have hstep : (fun ω : Ω =>
          ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ))
          = fun ω => ∑ i : Fin n, (if x < S ω i then (1 : ℝ) else 0) := by
        funext ω
        rw [Finset.card_filter]
        push_cast
        rfl
      rw [hstep]
      exact Finset.measurable_sum _ (fun i _ =>
        Measurable.ite (measurableSet_lt measurable_const (hSmeas i))
          measurable_const measurable_const)
    have hg_int : Integrable (fun ω : Ω => (2 * (n : ℝ))⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ)) μ := by
      refine MeasureTheory.Integrable.of_bound ?_ (1 / 2) ?_
      · exact (hcnt_meas.const_mul _).aestronglyMeasurable
      · filter_upwards with ω
        have h1 : ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ≤ (n : ℝ) := by
          have h := Finset.card_le_univ (s := Finset.univ.filter (fun i : Fin n => x < S ω i))
          rw [Fintype.card_fin] at h
          exact_mod_cast h
        have h0 : (0 : ℝ) ≤ (2 * (n : ℝ))⁻¹ := by positivity
        have h3 : (2 * (n : ℝ))⁻¹ * ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ)
            ≤ (2 * (n : ℝ))⁻¹ * (n : ℝ) := mul_le_mul_of_nonneg_left h1 h0
        have h2n : (2 * (n : ℝ))⁻¹ * (2 * (n : ℝ)) = 1 := by
          rw [inv_mul_cancel₀]
          positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (Nat.cast_nonneg _))]
        nlinarith only [h3, h2n]
    have hpt : ∀ ω : Ω, (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n => S ω i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n => -S ω i ≤ x)).card : ℝ))
        = 1 - (2 * (n : ℝ))⁻¹ *
          ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) := by
      intro ω
      have hB : (Finset.univ.filter (fun i : Fin n => -S ω i ≤ x)).card = n := by
        have h : (Finset.univ.filter (fun i : Fin n => -S ω i ≤ x)) = Finset.univ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          linarith [hS_nonneg ω i]
        rw [h, Finset.card_univ, Fintype.card_fin]
      have hA : ((Finset.univ.filter (fun i : Fin n => S ω i ≤ x)).card : ℝ)
          + ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) = (n : ℝ) := by
        have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
          (p := fun i : Fin n => S ω i ≤ x)
        rw [Finset.card_univ, Fintype.card_fin] at h
        have h2 : (Finset.filter (fun i : Fin n => ¬ S ω i ≤ x) Finset.univ)
            = Finset.univ.filter (fun i : Fin n => x < S ω i) :=
          Finset.filter_congr (fun i _ => by simp only [not_le])
        rw [h2] at h
        exact_mod_cast h
      have h2n : (2 * (n : ℝ))⁻¹ * (2 * (n : ℝ)) = 1 := by
        rw [inv_mul_cancel₀]
        positivity
      rw [hB, ← h2n, ← mul_sub]
      congr 1
      linarith only [hA]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hsub : ∫ ω : Ω, (1 - (2 * (n : ℝ))⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ)) ∂μ
        = 1 - ∫ ω : Ω, (2 * (n : ℝ))⁻¹ *
          ((Finset.univ.filter (fun i : Fin n => x < S ω i)).card : ℝ) ∂μ := by
      rw [integral_sub (integrable_const (1 : ℝ)) hg_int]
      simp
    rw [hsub]
    ring

  have hFA_lo : ∀ x : ℝ, x < 0 →
      (nuA (Set.Iic x)).toReal =
        ∫ ω, (2 * (n : ℝ))⁻¹ *
          ((Finset.univ.filter (fun i : Fin n => -x ≤ S ω i)).card : ℝ) ∂μ := by
    intro x hx
    simp only [S]
    rw [hnuA_cdf x]
    have hfun : (fun ω => (2 * (n : ℝ))⁻¹ *
        (((Finset.univ.filter (fun i : Fin n =>
            svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card : ℝ) +
          ((Finset.univ.filter (fun i : Fin n =>
            -(svals (maskedScaled p (Xi ω) (Mask ω)) i) ≤ x)).card : ℝ)))
        = fun ω => (2 * (n : ℝ))⁻¹ *
          ((Finset.univ.filter (fun i : Fin n =>
            -x ≤ svals (maskedScaled p (Xi ω) (Mask ω)) i)).card : ℝ) := by
      funext ω
      have hA : (Finset.univ.filter (fun i : Fin n =>
          svals (maskedScaled p (Xi ω) (Mask ω)) i ≤ x)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        linarith [hsvals_nonneg ω i]
      have hB : (Finset.univ.filter (fun i : Fin n =>
          -(svals (maskedScaled p (Xi ω) (Mask ω)) i) ≤ x)).card
          = (Finset.univ.filter (fun i : Fin n =>
            -x ≤ svals (maskedScaled p (Xi ω) (Mask ω)) i)).card := by
        have h : (Finset.univ.filter (fun i : Fin n =>
            -(svals (maskedScaled p (Xi ω) (Mask ω)) i) ≤ x))
            = (Finset.univ.filter (fun i : Fin n =>
              -x ≤ svals (maskedScaled p (Xi ω) (Mask ω)) i)) := by
          apply Finset.filter_congr
          intro i _
          constructor <;> intro hc <;> linarith
        rw [h]
      rw [hA, hB]
      simp
    rw [hfun]


  have hTr_int : Integrable Tr μ ∧ ∫ ω, Tr ω ∂μ = (n : ℝ) :=
    statopia_math_node_1012928599_c6ceb04b (μ := μ) (m := m) (n := n) (le_trans hn hnm) p hp0
      Xi Mask hXi_meas hXi_sq_int hXi_var hMask_meas hMask_val hMask_law hIndep
  have hS_meas : ∀ i : Fin n, Measurable fun ω => S ω i := hSmeas
  have hTr_sq_le : ∀ (ω : Ω) (i : Fin n), S ω i ≤ Real.sqrt (Tr ω) := by
    intro ω i
    have hmem : (S ω i) ^ 2 ≤ Tr ω := by
      simp only [Tr]
      exact Finset.single_le_sum (f := fun j : Fin n => (S ω j) ^ 2)
        (fun j _ => sq_nonneg (S ω j)) (Finset.mem_univ i)
    have h2 : Real.sqrt ((S ω i) ^ 2) ≤ Real.sqrt (Tr ω) := Real.sqrt_le_sqrt hmem
    rwa [Real.sqrt_sq (hS_nonneg ω i)] at h2
  have hint : ∀ i : Fin n, Integrable (fun ω => max (S ω i - 4) 0) μ := by
    intro i
    have hbound : ∀ ω : Ω, ‖max (S ω i - 4) 0‖ ≤ Tr ω + 1 := by
      intro ω
      have hTr_nn : (0 : ℝ) ≤ Tr ω := by
        simp only [Tr]
        exact Finset.sum_nonneg (fun j _ => sq_nonneg (S ω j))
      have h1 : max (S ω i - 4) 0 ≤ S ω i := max_le (by linarith) (hS_nonneg ω i)
      have h2 : S ω i ≤ Real.sqrt (Tr ω) := hTr_sq_le ω i
      have h3 : Real.sqrt (Tr ω) ≤ Tr ω + 1 := by
        nlinarith [Real.sq_sqrt hTr_nn, Real.sqrt_nonneg (Tr ω),
          sq_nonneg (Real.sqrt (Tr ω) - 1 / 2)]
      have h0 : (0 : ℝ) ≤ max (S ω i - 4) 0 := le_max_right _ _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      linarith
    have hmeas : AEStronglyMeasurable (fun ω => max (S ω i - 4) 0) μ :=
      (((hS_meas i).sub measurable_const).max measurable_const).aestronglyMeasurable
    exact MeasureTheory.Integrable.mono' (hTr_int.1.add (integrable_const (1 : ℝ))) hmeas
      (Filter.Eventually.of_forall hbound)
  have hEv_meas : MeasurableSet Ev := by
    simp only [Ev]
    exact MeasurableSet.iUnion (fun i : Fin n => measurableSet_lt measurable_const (hS_meas i))
  have hpoint : ∀ ω : Ω,
      ∑ i : Fin n, max (S ω i - 4) 0 ≤
        (if ω ∈ Ev then (1 : ℝ) else 0) * Real.sqrt ((n : ℝ) * Tr ω) := by
    intro ω
    have hterm : ∀ i : Fin n, max (S ω i - 4) 0 ≤ S ω i := by
      intro i
      exact max_le (by linarith) (hS_nonneg ω i)
    have hsum_le : ∑ i : Fin n, max (S ω i - 4) 0 ≤ ∑ i : Fin n, S ω i :=
      Finset.sum_le_sum (fun i _ => hterm i)
    by_cases hE : ω ∈ Ev
    · rw [if_pos hE, one_mul]
      have hCS : (∑ i : Fin n, S ω i) ^ 2 ≤ (n : ℝ) * Tr ω := by
        have h := sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin n))) (f := fun i => S ω i)
        simpa only [Finset.card_univ, Fintype.card_fin, Tr] using h
      have hsum_nonneg : 0 ≤ ∑ i : Fin n, S ω i :=
        Finset.sum_nonneg (fun i _ => hS_nonneg ω i)
      have hkey : ∑ i : Fin n, S ω i ≤ Real.sqrt ((n : ℝ) * Tr ω) := by
        have hsq : Real.sqrt ((∑ i : Fin n, S ω i) ^ 2) ≤ Real.sqrt ((n : ℝ) * Tr ω) :=
          Real.sqrt_le_sqrt hCS
        rwa [Real.sqrt_sq hsum_nonneg] at hsq
      exact le_trans hsum_le hkey
    · rw [if_neg hE, zero_mul]
      have hall : ∀ i : Fin n, S ω i ≤ 4 := by
        intro i
        by_contra hcon
        push_neg at hcon
        exact hE (by
          simp only [Ev, Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨i, hcon⟩)
      have hz : ∑ i : Fin n, max (S ω i - 4) 0 = 0 :=
        Finset.sum_eq_zero (fun i _ => max_eq_right (by linarith [hall i]))
      exact le_of_eq hz
  have hsqrt_pos : 0 < Real.sqrt eps := by
    nlinarith [Real.sq_sqrt heps_pos.le, Real.sqrt_nonneg eps, heps_pos]
  have hβpos : (0 : ℝ) < (n : ℝ) / Real.sqrt eps := div_pos hn0 hsqrt_pos
  have hβne : ((n : ℝ) / Real.sqrt eps) ≠ 0 := ne_of_gt hβpos
  have hTr_nonneg : ∀ ω : Ω, 0 ≤ Tr ω := by
    intro ω
    simp only [Tr]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (S ω i))
  have hAGM : ∀ x : ℝ, 0 ≤ x → Real.sqrt x
      ≤ (x / ((n : ℝ) / Real.sqrt eps) + (n : ℝ) / Real.sqrt eps) / 2 := by
    intro x hx
    have hnn : 0 ≤ (x / ((n : ℝ) / Real.sqrt eps) + (n : ℝ) / Real.sqrt eps) / 2 := by
      have h1 : 0 ≤ x / ((n : ℝ) / Real.sqrt eps) := div_nonneg hx hβpos.le
      linarith [hβpos]
    have hsq : x ≤ ((x / ((n : ℝ) / Real.sqrt eps) + (n : ℝ) / Real.sqrt eps) / 2) ^ 2 := by
      have e : ((x / ((n : ℝ) / Real.sqrt eps) + (n : ℝ) / Real.sqrt eps) / 2) ^ 2 - x
          = ((x / ((n : ℝ) / Real.sqrt eps) - (n : ℝ) / Real.sqrt eps) / 2) ^ 2 := by
        field_simp
        ring
      nlinarith [sq_nonneg ((x / ((n : ℝ) / Real.sqrt eps) - (n : ℝ) / Real.sqrt eps) / 2), e]
    have h2 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hnn] at h2
  have hyoung : ∀ ω : Ω,
      (if ω ∈ Ev then (1 : ℝ) else 0) * Real.sqrt ((n : ℝ) * Tr ω)
        ≤ ((n : ℝ) * Tr ω) / ((n : ℝ) / Real.sqrt eps) / 2
          + ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0) := by
    intro ω
    have hx0 : 0 ≤ (n : ℝ) * Tr ω := mul_nonneg hn0.le (hTr_nonneg ω)
    have hstep : ((n : ℝ) * Tr ω) / ((n : ℝ) / Real.sqrt eps) / 2
        + ((n : ℝ) / Real.sqrt eps) / 2
        = (((n : ℝ) * Tr ω) / ((n : ℝ) / Real.sqrt eps) + (n : ℝ) / Real.sqrt eps) / 2 := by
      ring
    by_cases h : ω ∈ Ev
    · simp only [if_pos h, one_mul, mul_one]
      rw [hstep]
      exact hAGM ((n : ℝ) * Tr ω) hx0
    · simp only [if_neg h, zero_mul, mul_zero, add_zero]
      exact div_nonneg (div_nonneg hx0 hβpos.le) (by norm_num)
  have hsum : ∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ ≤ (n : ℝ) * Real.sqrt eps := by
    have hsne : Real.sqrt eps ≠ 0 := ne_of_gt hsqrt_pos
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have hE_val : ∫ ω, (if ω ∈ Ev then (1 : ℝ) else 0) ∂μ = μ.real Ev := by
      have hid : (fun ω => (if ω ∈ Ev then (1 : ℝ) else 0))
          = Ev.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        rw [Set.indicator_apply]
      rw [hid, MeasureTheory.integral_indicator_const (s := Ev) (e := (1 : ℝ)) hEv_meas]
      simp
    have hE_int : Integrable (fun ω => (if ω ∈ Ev then (1 : ℝ) else 0)) μ := by
      refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
      · exact (Measurable.ite hEv_meas measurable_const measurable_const).aestronglyMeasurable
      · filter_upwards with ω
        by_cases h : ω ∈ Ev
        · rw [if_pos h]; norm_num
        · rw [if_neg h]; norm_num
    have hA_int : Integrable
        (fun ω => ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * Tr ω) μ :=
      hTr_int.1.const_mul _
    have hB_int : Integrable
        (fun ω => ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0)) μ :=
      hE_int.const_mul _
    have hmaj_int : Integrable (fun ω => ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * Tr ω
        + ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0)) μ :=
      hA_int.add hB_int
    have hsum_int : Integrable (fun ω => ∑ i : Fin n, max (S ω i - 4) 0) μ :=
      MeasureTheory.integrable_finset_sum Finset.univ (f := fun i ω => max (S ω i - 4) 0)
        (fun i _ => hint i)
    have hmaj_pt : ∀ ω : Ω, ∑ i : Fin n, max (S ω i - 4) 0
        ≤ ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * Tr ω
          + ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0) := by
      intro ω
      have heq : ((n : ℝ) * Tr ω) / ((n : ℝ) / Real.sqrt eps) / 2
          = ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * Tr ω := by ring
      calc ∑ i : Fin n, max (S ω i - 4) 0
          ≤ (if ω ∈ Ev then (1 : ℝ) else 0) * Real.sqrt ((n : ℝ) * Tr ω) := hpoint ω
        _ ≤ ((n : ℝ) * Tr ω) / ((n : ℝ) / Real.sqrt eps) / 2
              + ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0) := hyoung ω
        _ = ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * Tr ω
              + ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0) := by rw [heq]
    have hmono : ∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ
        ≤ ∫ ω, ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * Tr ω
            + ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0) ∂μ :=
      integral_mono hsum_int hmaj_int hmaj_pt
    have hsplit : ∫ ω, ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * Tr ω
            + ((n : ℝ) / Real.sqrt eps) / 2 * (if ω ∈ Ev then (1 : ℝ) else 0) ∂μ
        = ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * (n : ℝ)
          + ((n : ℝ) / Real.sqrt eps) / 2 * μ.real Ev := by
      rw [integral_add hA_int hB_int, integral_const_mul, integral_const_mul, hTr_int.2, hE_val]
    have hEvb : ((n : ℝ) / Real.sqrt eps) / 2 * μ.real Ev
        ≤ ((n : ℝ) / Real.sqrt eps) / 2 * eps :=
      mul_le_mul_of_nonneg_left hEv_real (by positivity)
    have hterm1 : ((n : ℝ) / ((n : ℝ) / Real.sqrt eps) / 2) * (n : ℝ)
        = (n : ℝ) * Real.sqrt eps / 2 := by
      field_simp
    have hterm2 : ((n : ℝ) / Real.sqrt eps) / 2 * eps = (n : ℝ) * Real.sqrt eps / 2 := by
      have hsq : Real.sqrt eps * Real.sqrt eps = eps := Real.mul_self_sqrt heps_pos.le
      field_simp
      nlinarith only [hsq]
    rw [hsplit] at hmono
    linarith only [hmono, hterm1, hEvb, hterm2]
  obtain ⟨hInt, hcore⟩ :=
    statopia_math_node_4274718050_2cbaed7c (Ω := Ω) (μ := μ) (n := n) (S := S) (nuA := nuA)
      (nuRho := nuRho) hn hS_meas hS_nonneg hint hFR_hi hFR_lo hFA_hi hFA_lo
  constructor
  · exact hInt
  · rw [hcore]
    have hsq : Real.sqrt eps = Real.rpow (n : ℝ) (-(D0 + 2) / 2) := by
      have h1 : Real.sqrt eps = Real.rpow (Real.rpow (n : ℝ) (-(D0 + 2))) (1 / 2) := by
        simp only [eps]
        exact Real.sqrt_eq_rpow _
      rw [h1]
      have h2 : Real.rpow (n : ℝ) (-(D0 + 2) * (1 / 2))
          = Real.rpow (Real.rpow (n : ℝ) (-(D0 + 2))) (1 / 2) :=
        Real.rpow_mul hn0.le (-(D0 + 2)) (1 / 2)
      rw [show -(D0 + 2) * (1 / 2) = -(D0 + 2) / 2 by ring] at h2
      exact h2.symm
    have h1 : (n : ℝ)⁻¹ * (∫ ω, ∑ i : Fin n, max (S ω i - 4) 0 ∂μ)
        ≤ (n : ℝ)⁻¹ * ((n : ℝ) * Real.sqrt eps) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : (n : ℝ)⁻¹ * ((n : ℝ) * Real.sqrt eps)
        = Real.rpow (n : ℝ) (-(D0 + 2) / 2) := by
      rw [← hsq, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn0), one_mul]
    rw [h2] at h1
    exact h1
  /- @proof-region region.target-node.session.07ec289ce396e95d end -/

end Statlib.Imported

