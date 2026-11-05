import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_2526795459_802d95db_38e28795
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3502754207_ce139dc9_93b059d6
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3585068469_28420a32_d25d4598
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4000542074_30367f47_51acbb0f
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4242285578_94052d98_2e612b35
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_512556819_d2fb8272_61934352



open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_2469337524_a68c5ec1 : ∀ {X Y U Θ V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
    [TopologicalSpace.SeparableSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V] [MeasurableSpace V] [BorelSpace V]
    (M : Model X Y U Θ V)
    (hℓ : Measurable (Function.uncurry M.ℓ))
    (HP : ProbabilityMeasure Θ)
    (lam gam : ℝ) (hlam : 0 < lam) (hgam : 0 < gam)
    (n : ℕ) (hn : 0 < n)
    (𝒯 : ProbabilityMeasure (ProbabilityMeasure (X × Y) × ℕ+))
    (ω : Fin n → Block (X × Y))
    (𝒬 : ProbabilityMeasure Θ)
    (hPrior_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ =>
      basePrior M k q.1 q.2)
    (hPost_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ =>
      basePost M k q.1 q.2)
    (hKL_meas : ∀ (k : ℕ) (S : Fin k → X × Y), Measurable fun θ : Θ =>
      InformationTheory.klDiv (basePost M k S θ : Measure U) (basePrior M k S θ : Measure U))
    (hℓ_int : ∀ (u : U) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun z : X × Y => M.ℓ u z) (D : Measure (X × Y)))
    (hLgibbs_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun u : U => Lmean M.ℓ u (D : Measure (X × Y))) (basePost M k S θ : Measure U))
    (hLgibbsEmp_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ),
      Integrable (fun u : U => Lemp M.ℓ u S) (basePost M k S θ : Measure U))
    (hTransferLoss_int : ∀ (𝒬' : ProbabilityMeasure Θ),
      Integrable (fun θ : Θ =>
        ∫ p, transferAt M θ p ∂(𝒯 : Measure (ProbabilityMeasure (X × Y) × ℕ+))) (𝒬' : Measure Θ))
    (hEmpMulti_int : ∀ (𝒬' : ProbabilityMeasure Θ) (ω' : Fin n → Block (X × Y)),
      Integrable (fun θ : Θ => (1 / (n : ℝ)) * ∑ i : Fin n,
        LgibbsEmp M.ℓ (basePost M ((mOf ω' i : ℕ)) (SOF ω' i) θ : Measure U) (SOF ω' i))
        (𝒬' : Measure Θ))
    (hPi1Exp_int : ∀ (ω' : Fin n → Block (X × Y)) (θ : Θ),
      Integrable (Pi1Exp M n gam ω' θ)
        (Measure.pi fun i : Fin n => (basePrior M ((mOf ω' i : ℕ)) (SOF ω' i) θ : Measure U)))
    (hPi1Inner_int : ∀ ω' : Fin n → Block (X × Y),
      Integrable (fun θ : Θ => Pi1Inner M n gam ω' θ) (HP : Measure Θ))
    (hPi2Exp_int : ∀ ω' : Fin n → Block (X × Y),
      Integrable (fun θ : Θ => Pi2Exp M n 𝒯 lam ω' θ) (HP : Measure Θ))
    (hKfin : ENNReal.toEReal (InformationTheory.klDiv (𝒬 : Measure Θ) (HP : Measure Θ)) ≠ ⊤)
    (hBfin : baseKLSum M n 𝒬 ω ≠ ⊤),
    let phi : Θ × (Fin n → U) → ℝ := fun x =>
      (1 / (n : ℝ)) * ∑ i : Fin n,
        (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i))
    let G : Θ → ℝ := fun θ =>
      (1 / (n : ℝ)) * ∑ i : Fin n,
        Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
          (DOf ω i : Measure (X × Y))
    let nu : Measure (Θ × (Fin n → U)) := (𝒬 : Measure Θ).bind (fun θ =>
      (Measure.pi fun i : Fin n =>
        (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
        (fun u : Fin n → U => (θ, u)))
    Integrable G (𝒬 : Measure Θ) ∧
      Integrable phi nu ∧
      (∫ x, phi x ∂nu = (∫ θ, G θ ∂(𝒬 : Measure Θ)) - empMulti M n 𝒬 ω) ∧
      (𝒬 : Measure Θ) ≪ (HP : Measure Θ) := by
  /- @proof-region region.target-node.session.ac23a9ccfa096dbc begin -/
  intro X Y U Θ V
    iX1 iX2 iX3 iX4 iX5 iX6
    iY1 iY2 iY3 iY4 iY5 iY6
    iU1 iU2 iU3 iU4 iU5 iU6
    iT1 iT2 iT3 iT4 iT5 iT6
    iV1 iV2 iV3 iV4 iV5 iV6
  intro M hℓ HP lam gam hlam hgam n hn 𝒯 ω 𝒬 hPrior_meas hPost_meas hKL_meas
    hℓ_int hLgibbs_int hLgibbsEmp_int hTransferLoss_int hEmpMulti_int hPi1Exp_int
    hPi1Inner_int hPi2Exp_int hKfin hBfin
  let phi : Θ × (Fin n → U) → ℝ := fun x =>
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF ω i))
  let G : Θ → ℝ := fun θ =>
    (1 / (n : ℝ)) * ∑ i : Fin n,
      Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
        (DOf ω i : Measure (X × Y))
  let GE : Θ → ℝ := fun θ =>
    (1 / (n : ℝ)) * ∑ i : Fin n,
      LgibbsEmp M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (SOF ω i)
  let nu : Measure (Θ × (Fin n → U)) := (𝒬 : Measure Θ).bind (fun θ =>
    (Measure.pi fun i : Fin n =>
      (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
      (fun u : Fin n → U => (θ, u)))
  have hemp : empMulti M n 𝒬 ω = ∫ θ, GE θ ∂(𝒬 : Measure Θ) := rfl
  have hGEint : Integrable GE (𝒬 : Measure Θ) := hEmpMulti_int 𝒬 ω
  have hPm : ∀ i : Fin n, Measurable fun θ : Θ =>
      (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) := by
    intro i
    have hpair : Measurable fun θ : Θ =>
        ((SOF ω i : Fin ((mOf ω i : ℕ)) → X × Y), θ) :=
      measurable_const.prodMk measurable_id
    have h0 : Measurable fun θ : Θ =>
        basePost M ((mOf ω i : ℕ)) (SOF ω i) θ :=
      (hPost_meas (mOf ω i : ℕ)).comp hpair
    exact measurable_subtype_coe.comp h0
  have hchild := statopia_math_node_4242285578_94052d98 M hℓ 𝒬 n hn ω
    hLgibbs_int hLgibbsEmp_int hPm
  obtain ⟨hfib, hTonP, hTonN, hcmpP, hcmpN, hmain⟩ := hchild
  have hfibInt : ∀ θ : Θ, Integrable (fun u : Fin n → U => phi (θ, u))
      (Measure.pi fun i : Fin n => (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) :=
    fun θ => (hfib θ).1
  have hfibVal : ∀ θ : Θ, ∫ u : Fin n → U, phi (θ, u)
      ∂(Measure.pi fun i : Fin n => (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))
      = G θ - GE θ :=
    fun θ => (hfib θ).2
  let mu : Measure (Θ × (Fin n → U)) := (HP : Measure Θ).bind (fun θ =>
    (Measure.pi fun i : Fin n =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
      (fun u : Fin n → U => (θ, u)))
  have hPr : ∀ i : Fin n, Measurable fun θ : Θ =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) := by
    intro i
    have hpair : Measurable fun θ : Θ =>
        ((SOF ω i : Fin ((mOf ω i : ℕ)) → X × Y), θ) :=
      measurable_const.prodMk measurable_id
    exact measurable_subtype_coe.comp ((hPrior_meas (mOf ω i : ℕ)).comp hpair)
  have hexp := statopia_math_node_512556819_d2fb8272 M hℓ hℓ_int hLgibbs_int
    hLgibbsEmp_int HP gam hgam n hn ω (fun θ => hPi1Exp_int ω θ) (hPi1Inner_int ω) hPr
  obtain ⟨hφmeas, hexpint, hexpval⟩ := hexp
  let T : Θ → ℝ := fun θ =>
    ∫ p, transferAt M θ p ∂(𝒯 : Measure (ProbabilityMeasure (X × Y) × ℕ+))
  have hPi2eq : ∀ θ : Θ, Pi2Exp M n 𝒯 lam ω θ = Real.exp (lam * (T θ - G θ)) := by
    intro θ
    have hnR : (n : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact ne_of_gt hpos
    simp only [Pi2Exp]
    congr 1
    simp only [T, G]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  have hPi2bdd : ∀ θ : Θ,
      Real.exp (lam * max (T θ - G θ) 0) ≤ 1 + Pi2Exp M n 𝒯 lam ω θ := by
    intro θ
    rw [hPi2eq θ]
    have hpos : 0 < Real.exp (lam * (T θ - G θ)) := Real.exp_pos _
    rw [max_def]
    split_ifs with h
    · rw [mul_zero, Real.exp_zero]
      linarith
    · linarith
  have hexpbdd : ∀ x : Θ × (Fin n → U),
      Real.exp (gam * max (phi x) 0) ≤ 1 + Real.exp (gam * phi x) := by
    intro x
    have hpos : 0 < Real.exp (gam * phi x) := Real.exp_pos _
    rw [max_def]
    split_ifs with h
    · rw [mul_zero, Real.exp_zero]
      linarith
    · linarith
  have hφpos : Measurable fun x : Θ × (Fin n → U) => max (phi x) 0 :=
    hφmeas.max measurable_const
  have hGpoint : ∀ θ : Θ,
      ENNReal.ofReal (G θ) ≤ ENNReal.ofReal (G θ - GE θ) + ENNReal.ofReal (GE θ) := by
    intro θ
    have h : ENNReal.ofReal ((G θ - GE θ) + GE θ)
        ≤ ENNReal.ofReal (G θ - GE θ) + ENNReal.ofReal (GE θ) := ENNReal.ofReal_add_le
    rwa [sub_add_cancel] at h
  have hpiQ_prob : ∀ θ : Θ, IsProbabilityMeasure (Measure.pi fun i : Fin n =>
      (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) := by
    intro θ
    infer_instance
  have hpiP_prob : ∀ θ : Θ, IsProbabilityMeasure (Measure.pi fun i : Fin n =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) := by
    intro θ
    infer_instance
  have hmapQ_prob : ∀ θ : Θ, IsProbabilityMeasure (Measure.map
      (fun u : Fin n → U => (θ, u))
      (Measure.pi fun i : Fin n => (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) := by
    intro θ
    exact Measure.isProbabilityMeasure_map (measurable_const.prodMk measurable_id).aemeasurable
  have hmapP_prob : ∀ θ : Θ, IsProbabilityMeasure (Measure.map
      (fun u : Fin n → U => (θ, u))
      (Measure.pi fun i : Fin n => (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) := by
    intro θ
    exact Measure.isProbabilityMeasure_map (measurable_const.prodMk measurable_id).aemeasurable
  have hGup : ∫⁻ θ, ENNReal.ofReal (G θ) ∂(𝒬 : Measure Θ)
      ≤ ∫⁻ θ, (ENNReal.ofReal (G θ - GE θ) + ENNReal.ofReal (GE θ))
          ∂(𝒬 : Measure Θ) :=
    lintegral_mono fun θ => hGpoint θ
  have hGpoint' : ∀ θ : Θ,
      ENNReal.ofReal (-(G θ))
        ≤ ENNReal.ofReal (-(G θ - GE θ)) + ENNReal.ofReal (-(GE θ)) := by
    intro θ
    have h : ENNReal.ofReal ((-(G θ - GE θ)) + (-(GE θ)))
        ≤ ENNReal.ofReal (-(G θ - GE θ)) + ENNReal.ofReal (-(GE θ)) :=
      ENNReal.ofReal_add_le
    have h2 : -(G θ - GE θ) + -(GE θ) = -(G θ) := by ring
    rwa [h2] at h
  have hKLchain : ENNReal.toEReal (InformationTheory.klDiv nu mu)
      = ENNReal.toEReal (InformationTheory.klDiv (𝒬 : Measure Θ) (HP : Measure Θ))
        + baseKLSum M n 𝒬 ω := by
    haveI : MeasurableSpace.CountableOrCountablyGenerated Θ (Fin n → U) := inferInstance
    exact statopia_math_node_2526795459_802d95db M HP 𝒬 n hn ω hPr hPm
      (fun i => hKL_meas (mOf ω i : ℕ) (SOF ω i))
  have hTint : Integrable T (𝒬 : Measure Θ) := hTransferLoss_int 𝒬
  have hpiQ_univ : ∀ θ : Θ, (Measure.pi fun i : Fin n =>
      (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) Set.univ = 1 := by
    intro θ
    rw [Measure.pi_univ]
    simp
  have hpiP_univ : ∀ θ : Θ, (Measure.pi fun i : Fin n =>
      (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) Set.univ = 1 := by
    intro θ
    rw [Measure.pi_univ]
    simp
  obtain ⟨hνprob, hμprob⟩ := statopia_math_node_3502754207_ce139dc9 M n hn ω 𝒬 HP hPm hPr
  haveI hνprobI : IsProbabilityMeasure nu := hνprob
  haveI hμprobI : IsProbabilityMeasure mu := hμprob
  have hconst1 : Integrable (fun _ : Θ × (Fin n → U) => (1 : ℝ)) mu := integrable_const 1
  have hbound : Integrable (fun x : Θ × (Fin n → U) => Real.exp (gam * phi x) + 1) mu :=
    hexpint.add hconst1
  have hexpP : Integrable (fun x : Θ × (Fin n → U) => Real.exp (gam * max (phi x) 0)) mu := by
    refine Integrable.mono' hbound ?_ ?_
    · exact ((measurable_const.mul hφpos).exp).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have h1 := hexpbdd x
      have h2 : (0 : ℝ) < Real.exp (gam * max (phi x) 0) := Real.exp_pos _
      rw [Real.norm_eq_abs, abs_of_pos h2]
      linarith
  have hgam_ne : gam ≠ 0 := ne_of_gt hgam
  have hengine := statopia_math_node_4000542074_30367f47
    (⟨mu, hμprob⟩ : ProbabilityMeasure (Θ × (Fin n → U)))
    (⟨nu, hνprob⟩ : ProbabilityMeasure (Θ × (Fin n → U)))
    gam hgam (fun x : Θ × (Fin n → U) => max (phi x) 0) hφpos hexpP
  have hφof : ∀ x : Θ × (Fin n → U),
      ENNReal.ofReal (max (phi x) 0) = ENNReal.ofReal (phi x) := by
    intro x
    rw [max_def]
    split_ifs with h
    · rw [ENNReal.ofReal_eq_zero.mpr h]
      exact ENNReal.ofReal_eq_zero.mpr (le_refl (0 : ℝ))
    · rfl
  have hφlin : ∫⁻ x, ENNReal.ofReal (max (phi x) 0) ∂nu
      = ∫⁻ x, ENNReal.ofReal (phi x) ∂nu :=
    lintegral_congr fun x => hφof x
  have hneg0 : ∀ x : Θ × (Fin n → U), ENNReal.ofReal (-(max (phi x) 0)) = 0 := by
    intro x
    have h : (0 : ℝ) ≤ max (phi x) 0 := le_max_right _ _
    exact ENNReal.ofReal_eq_zero.mpr (by linarith)
  have hneglin : ∫⁻ x, ENNReal.ofReal (-(max (phi x) 0)) ∂nu = 0 := by
    simp only [hneg0]
    simp
  have hφaesm : AEStronglyMeasurable phi nu := hφmeas.aestronglyMeasurable
  have hGupN : ∫⁻ θ, ENNReal.ofReal (-(G θ)) ∂(𝒬 : Measure Θ)
      ≤ ∫⁻ θ, (ENNReal.ofReal (-(G θ - GE θ)) + ENNReal.ofReal (-(GE θ)))
          ∂(𝒬 : Measure Θ) :=
    lintegral_mono fun θ => hGpoint' θ
  have hQtranP : (∫⁻ x, ENNReal.ofReal (phi x) ∂nu) < ⊤ →
      (∫⁻ θ, ENNReal.ofReal (G θ - GE θ) ∂(𝒬 : Measure Θ)) < ⊤ :=
    fun h => lt_of_le_of_lt hcmpP h
  have hQtranN : (∫⁻ x, ENNReal.ofReal (-(phi x)) ∂nu) < ⊤ →
      (∫⁻ θ, ENNReal.ofReal (-(G θ - GE θ)) ∂(𝒬 : Measure Θ)) < ⊤ :=
    fun h => lt_of_le_of_lt hcmpN h
  have hGfinP : (∫⁻ θ, (ENNReal.ofReal (G θ - GE θ) + ENNReal.ofReal (GE θ))
        ∂(𝒬 : Measure Θ)) < ⊤ →
      (∫⁻ θ, ENNReal.ofReal (G θ) ∂(𝒬 : Measure Θ)) < ⊤ :=
    fun h => lt_of_le_of_lt hGup h
  have hGfinN : (∫⁻ θ, (ENNReal.ofReal (-(G θ - GE θ)) + ENNReal.ofReal (-(GE θ)))
        ∂(𝒬 : Measure Θ)) < ⊤ →
      (∫⁻ θ, ENNReal.ofReal (-(G θ)) ∂(𝒬 : Measure Θ)) < ⊤ :=
    fun h => lt_of_le_of_lt hGupN h
  have hφnegof : ∀ x : Θ × (Fin n → U),
      ENNReal.ofReal (max (-(phi x)) 0) = ENNReal.ofReal (-(phi x)) := by
    intro x
    rw [max_def]
    split_ifs with h
    · rw [ENNReal.ofReal_eq_zero.mpr h]
      exact ENNReal.ofReal_eq_zero.mpr (le_refl (0 : ℝ))
    · rfl
  have hφneglin : ∫⁻ x, ENNReal.ofReal (max (-(phi x)) 0) ∂nu
      = ∫⁻ x, ENNReal.ofReal (-(phi x)) ∂nu :=
    lintegral_congr fun x => hφnegof x
  obtain ⟨hGint, hφint⟩ := statopia_math_node_3585068469_28420a32 M hℓ HP lam gam
    hlam hgam n hn 𝒯 ω 𝒬 hPrior_meas hPost_meas hKL_meas hℓ_int hLgibbs_int
    hLgibbsEmp_int hTransferLoss_int hEmpMulti_int hPi1Exp_int hPi1Inner_int
    hPi2Exp_int hKfin hBfin
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hGint
  · exact hφint
  · have hsub := (hmain hφint).2
    have hdiff : ∫ θ, (G θ - GE θ) ∂(𝒬 : Measure Θ)
        = (∫ θ, G θ ∂(𝒬 : Measure Θ)) - ∫ θ, GE θ ∂(𝒬 : Measure Θ) :=
      integral_sub hGint hGEint
    rw [hsub, hdiff, hemp]
  · by_contra hns
    have htop : InformationTheory.klDiv (𝒬 : Measure Θ) (HP : Measure Θ) = ⊤ := by
      simp [InformationTheory.klDiv, hns]
    exact hKfin (by rw [htop]; simp)
  /- @proof-region region.target-node.session.ac23a9ccfa096dbc end -/

end
end Statlib.Imported
