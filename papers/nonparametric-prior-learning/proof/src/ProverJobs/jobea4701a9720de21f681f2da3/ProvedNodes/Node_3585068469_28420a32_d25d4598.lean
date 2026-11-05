import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_1040909254_bc7c3bc1_0ecaf73d
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_2526795459_802d95db_38e28795
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_3502754207_ce139dc9_93b059d6
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4000542074_30367f47_51acbb0f
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4065279287_e9ac2bcb_a50d0647
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4096909918_1936c781_4cef37d3
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
theorem statopia_math_node_3585068469_28420a32 : ∀ {X Y U Θ V : Type*}
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
    (hEll : Measurable (Function.uncurry M.ℓ))
    (HP : ProbabilityMeasure Θ)
    (lam gam : ℝ) (hlam : 0 < lam) (hgam : 0 < gam)
    (n : ℕ) (hn : 0 < n)
    (calT : ProbabilityMeasure (ProbabilityMeasure (X × Y) × ℕ+))
    (omega : Fin n → Block (X × Y))
    (calQ : ProbabilityMeasure Θ)
    (hPrior_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ => basePrior M k q.1 q.2)
    (hPost_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ => basePost M k q.1 q.2)
    (hKL_meas : ∀ (k : ℕ) (S : Fin k → X × Y), Measurable fun θ : Θ =>
      InformationTheory.klDiv (basePost M k S θ : Measure U) (basePrior M k S θ : Measure U))
    (hL_int : ∀ (u : U) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun z : X × Y => M.ℓ u z) (D : Measure (X × Y)))
    (hLgibbs_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun u : U => Lmean M.ℓ u (D : Measure (X × Y))) (basePost M k S θ : Measure U))
    (hLgibbsEmp_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ),
      Integrable (fun u : U => Lemp M.ℓ u S) (basePost M k S θ : Measure U))
    (hTransferLoss_int : ∀ (calQ' : ProbabilityMeasure Θ),
      Integrable (fun θ : Θ =>
        ∫ p, transferAt M θ p ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
        (calQ' : Measure Θ))
    (hEmpMulti_int : ∀ (calQ' : ProbabilityMeasure Θ) (omega' : Fin n → Block (X × Y)),
      Integrable (fun θ : Θ => (1 / (n : ℝ)) * ∑ i : Fin n,
        LgibbsEmp M.ℓ (basePost M ((mOf omega' i : ℕ)) (SOF omega' i) θ : Measure U)
          (SOF omega' i))
        (calQ' : Measure Θ))
    (hPi1Exp_int : ∀ (omega' : Fin n → Block (X × Y)) (θ : Θ),
      Integrable (Pi1Exp M n gam omega' θ)
        (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf omega' i : ℕ)) (SOF omega' i) θ : Measure U)))
    (hPi1Inner_int : ∀ (omega' : Fin n → Block (X × Y)),
      Integrable (fun θ : Θ => Pi1Inner M n gam omega' θ) (HP : Measure Θ))
    (hPi2Exp_int : ∀ (omega' : Fin n → Block (X × Y)),
      Integrable (fun θ : Θ => Pi2Exp M n calT lam omega' θ) (HP : Measure Θ))
    (hKfin : ENNReal.toEReal (InformationTheory.klDiv (calQ : Measure Θ) (HP : Measure Θ)) ≠ ⊤)
    (hBfin : baseKLSum M n calQ omega ≠ ⊤),
    (let phi : Θ × (Fin n → U) → ℝ := fun x =>
        (1 / (n : ℝ)) * ∑ i : Fin n,
          (Lmean M.ℓ (x.2 i) (DOf omega i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF omega i))
     let GE : Θ → ℝ := fun θ =>
        (1 / (n : ℝ)) * ∑ i : Fin n,
          LgibbsEmp M.ℓ (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
            (SOF omega i)
     let G : Θ → ℝ := fun θ =>
        (1 / (n : ℝ)) * ∑ i : Fin n,
          Lgibbs M.ℓ (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
            (DOf omega i : Measure (X × Y))
     let nu : Measure (Θ × (Fin n → U)) :=
        (calQ : Measure Θ).bind (fun θ =>
          (Measure.pi fun i : Fin n =>
            (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)).map
              (fun u : Fin n → U => (θ, u)))
     let T : Θ → ℝ := fun θ =>
        ∫ p, transferAt M θ p ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+))
     Integrable G (calQ : Measure Θ) ∧ Integrable phi nu) := by
  /- @proof-region region.target-node.session.78b19b16c8486232 begin -/
  intro X Y U Θ V
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro M hEll HP lam gam hlam hgam n hn calT omega calQ
  intro hPrior_meas hPost_meas hKL_meas hL_int hLgibbs_int hLgibbsEmp_int
  intro hTransferLoss_int hEmpMulti_int hPi1Exp_int hPi1Inner_int hPi2Exp_int hKfin hBfin
  let phi : Θ × (Fin n → U) → ℝ := fun x =>
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Lmean M.ℓ (x.2 i) (DOf omega i : Measure (X × Y)) - Lemp M.ℓ (x.2 i) (SOF omega i))
  let GE : Θ → ℝ := fun θ =>
    (1 / (n : ℝ)) * ∑ i : Fin n,
      LgibbsEmp M.ℓ (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) (SOF omega i)
  let G : Θ → ℝ := fun θ =>
    (1 / (n : ℝ)) * ∑ i : Fin n,
      Lgibbs M.ℓ (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
        (DOf omega i : Measure (X × Y))
  let nu : Measure (Θ × (Fin n → U)) :=
    (calQ : Measure Θ).bind (fun θ =>
      (Measure.pi fun i : Fin n =>
        (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)).map
          (fun u : Fin n → U => (θ, u)))
  let mu : Measure (Θ × (Fin n → U)) :=
    (HP : Measure Θ).bind (fun θ =>
      (Measure.pi fun i : Fin n =>
        (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)).map
          (fun u : Fin n → U => (θ, u)))
  let T : Θ → ℝ := fun θ =>
    ∫ p, transferAt M θ p ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+))
  change Integrable G (calQ : Measure Θ) ∧ Integrable phi nu
  have pmE : ∀ i : Fin n, Measurable fun θ : Θ => (SOF omega i, θ) :=
    fun i => Measurable.prodMk (measurable_const : Measurable fun _ : Θ => SOF omega i) measurable_id
  have erA : ∀ r : ℝ, ((r : ℝ) : EReal) ≠ ⊤ := fun r h => by cases h
  have ccg : MeasurableSpace.CountableOrCountablyGenerated Θ (Fin n → U) := inferInstance
  have hPm : ∀ i : Fin n, Measurable fun θ : Θ =>
      (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) := by
    intro i
    exact measurable_subtype_coe.comp ((hPost_meas ((mOf omega i : ℕ))).comp (pmE i))
  have hPr : ∀ i : Fin n, Measurable fun θ : Θ =>
      (basePrior M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U) := by
    intro i
    exact measurable_subtype_coe.comp ((hPrior_meas ((mOf omega i : ℕ))).comp (pmE i))
  have hpack : IsProbabilityMeasure nu ∧ IsProbabilityMeasure mu :=
    statopia_math_node_3502754207_ce139dc9 M n hn omega calQ HP hPm hPr
  have hνprob : IsProbabilityMeasure nu := hpack.1
  have hμprob : IsProbabilityMeasure mu := hpack.2
  have h512 := statopia_math_node_512556819_d2fb8272 M hEll hL_int hLgibbs_int hLgibbsEmp_int
    HP gam hgam n hn omega (fun θ => hPi1Exp_int omega θ) (hPi1Inner_int omega) hPr
  have hφmeas : Measurable phi := h512.1
  have hexpint : Integrable (fun x : Θ × (Fin n → U) => Real.exp (gam * phi x)) mu := h512.2.1
  have hKLchain := statopia_math_node_2526795459_802d95db M HP calQ n hn omega hPr hPm
    (fun i => hKL_meas ((mOf omega i : ℕ)) (SOF omega i))
  have hGEint : Integrable GE (calQ : Measure Θ) :=
    hEmpMulti_int calQ omega
  have hTint : Integrable T (calQ : Measure Θ) :=
    hTransferLoss_int calQ
  haveI : IsProbabilityMeasure nu := hνprob
  haveI : IsProbabilityMeasure mu := hμprob
  have hνP : ProbabilityMeasure (Θ × (Fin n → U)) := ⟨nu, hνprob⟩
  have hμP : ProbabilityMeasure (Θ × (Fin n → U)) := ⟨mu, hμprob⟩
  have hexpbnd : ∀ x : Θ × (Fin n → U),
      Real.exp (gam * max (phi x) 0) ≤ 1 + Real.exp (gam * phi x) := by
    intro x
    rcases le_total 0 (phi x) with h | h
    · rw [max_eq_left h]
      linarith [Real.exp_pos (gam * phi x)]
    · rw [max_eq_right h, mul_zero, Real.exp_zero]
      linarith [Real.exp_pos (gam * phi x)]
  have hmφmax : Measurable fun x : Θ × (Fin n → U) => max (phi x) 0 :=
    hφmeas.max measurable_const
  have hmexp : Measurable fun x : Θ × (Fin n → U) => Real.exp (gam * max (phi x) 0) :=
    Real.measurable_exp.comp
      (((measurable_const : Measurable fun _ : Θ × (Fin n → U) => gam)).mul hmφmax)
  have hExpMaj : Integrable
      ((fun x : Θ × (Fin n → U) => Real.exp (gam * phi x)) + fun _ => (1 : ℝ)) mu :=
    hexpint.add (integrable_const (1 : ℝ))
  have hexpP : Integrable (fun x : Θ × (Fin n → U) => Real.exp (gam * max (phi x) 0)) mu := by
    refine Integrable.mono' hExpMaj hmexp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ‖Real.exp (gam * max (phi x) 0)‖ = Real.exp (gam * max (phi x) 0) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [h1, Pi.add_apply]
    show Real.exp (gam * max (phi x) 0) ≤ Real.exp (gam * phi x) + 1
    linarith [hexpbnd x]
  have hengine := statopia_math_node_4000542074_30367f47 ⟨mu, hμprob⟩ ⟨nu, hνprob⟩ gam hgam
    (fun x : Θ × (Fin n → U) => max (phi x) 0) hmφmax hexpP
  have hFub := statopia_math_node_4242285578_94052d98 M hEll calQ n hn omega
    hLgibbs_int hLgibbsEmp_int hPm
  have hofmaxR : ∀ t : ℝ, ENNReal.ofReal (max t 0) = ENNReal.ofReal t := by
    intro t
    rcases le_total 0 t with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_zero]
      exact (ENNReal.ofReal_eq_zero.mpr h).symm
  have hφposfin : (∫⁻ x, ENNReal.ofReal (phi x) ∂nu) ≠ ⊤ := by
    have hpos : (∫⁻ x, ENNReal.ofReal (max (phi x) 0) ∂nu) ≠ ⊤ :=
      statopia_math_node_1040909254_bc7c3bc1 ⟨mu, hμprob⟩ ⟨nu, hνprob⟩ gam hgam
        (fun x : Θ × (Fin n → U) => max (phi x) 0) hmφmax (fun x => le_max_right _ _) hexpP
        (ENNReal.toEReal (InformationTheory.klDiv (calQ : Measure Θ) (HP : Measure Θ)))
        (baseKLSum M n calQ omega) hKfin hBfin hKLchain
    have he : (∫⁻ x, ENNReal.ofReal (phi x) ∂nu)
        = (∫⁻ x, ENNReal.ofReal (max (phi x) 0) ∂nu) :=
      lintegral_congr fun x => (hofmaxR (phi x)).symm
    rw [he]
    exact hpos
  have hPi2eq : ∀ θ : Θ, Real.exp (lam * (T θ - G θ)) = Pi2Exp M n calT lam omega θ := by
    intro θ
    unfold Pi2Exp
    have hT : T θ = ∫ p, transferAt M θ p ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+)) :=
      rfl
    have hG : G θ = (1 / (n : ℝ)) * ∑ i : Fin n,
        Lgibbs M.ℓ (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
          (DOf omega i : Measure (X × Y)) := rfl
    rw [hT, hG]
    have hsum : (∑ i : Fin n, ((∫ p, transferAt M θ p
        ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
        - Lgibbs M.ℓ (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
            (DOf omega i : Measure (X × Y))))
        = (n : ℝ) * (∫ p, transferAt M θ p
            ∂(calT : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
          - ∑ i : Fin n, Lgibbs M.ℓ (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)
              (DOf omega i : Measure (X × Y)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    rw [hsum]
    congr 1
    have hnR : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hMTG0 := statopia_math_node_4096909918_1936c781 M hEll n hn omega calT
    hPost_meas hL_int hLgibbs_int
  have hMG : Measurable G := hMTG0.1
  have hMT : Measurable T := hMTG0.2
  have hMTG : Measurable fun θ : Θ => max (T θ - G θ) 0 :=
    (hMT.sub hMG).max measurable_const
  have hPi2bnd : ∀ θ : Θ,
      Real.exp (lam * max (T θ - G θ) 0) = max (Pi2Exp M n calT lam omega θ) 1 := by
    intro θ
    rw [← hPi2eq θ]
    rcases le_total 0 (T θ - G θ) with h | h
    · rw [max_eq_left h]
      exact (max_eq_left (show (1 : ℝ) ≤ Real.exp (lam * (T θ - G θ)) by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg hlam.le h))).symm
    · rw [max_eq_right h, mul_zero, Real.exp_zero]
      exact (max_eq_right (show Real.exp (lam * (T θ - G θ)) ≤ 1 by
        rw [← Real.exp_zero]
        have h2 : (0 : ℝ) ≤ lam * (-(T θ - G θ)) := mul_nonneg hlam.le (by linarith)
        exact Real.exp_le_exp.mpr (by nlinarith))).symm
  have hExpMmeas : Measurable fun θ : Θ => Real.exp (lam * max (T θ - G θ) 0) :=
    Real.measurable_exp.comp
      (((measurable_const : Measurable fun _ : Θ => lam)).mul hMTG)
  have hExpMajM : Integrable
      ((fun θ : Θ => Pi2Exp M n calT lam omega θ) + fun _ => (1 : ℝ)) (HP : Measure Θ) :=
    (hPi2Exp_int omega).add (integrable_const (1 : ℝ))
  have hexpM : Integrable (fun θ : Θ => Real.exp (lam * max (T θ - G θ) 0)) (HP : Measure Θ) := by
    refine Integrable.mono' hExpMajM hExpMmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => ?_)
    have hp : (0 : ℝ) < Pi2Exp M n calT lam omega θ := by
      unfold Pi2Exp
      exact Real.exp_pos _
    have h1 : ‖Real.exp (lam * max (T θ - G θ) 0)‖ = Real.exp (lam * max (T θ - G θ) 0) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [h1, hPi2bnd θ, Pi.add_apply]
    show max (Pi2Exp M n calT lam omega θ) 1 ≤ Pi2Exp M n calT lam omega θ + 1
    exact max_le (by linarith) (by linarith)
  have hengineM := statopia_math_node_4000542074_30367f47 HP calQ lam hlam
    (fun θ : Θ => max (T θ - G θ) 0) hMTG hexpM
  have hM1 : (∫⁻ θ, ENNReal.ofReal (max (T θ - G θ) 0) ∂(calQ : Measure Θ)) ≠ ⊤ := by
    refine statopia_math_node_1040909254_bc7c3bc1 HP calQ lam hlam
      (fun θ : Θ => max (T θ - G θ) 0) hMTG (fun θ => le_max_right _ _) hexpM
      (ENNReal.toEReal (InformationTheory.klDiv (calQ : Measure Θ) (HP : Measure Θ))) 0 hKfin ?_ ?_
    · exact erA 0
    · simp
  have hTnegfin : (∫⁻ θ, ENNReal.ofReal (max (-(T θ)) 0) ∂(calQ : Measure Θ)) < ⊤ := by
    have hb : ∀ θ : Θ, ENNReal.ofReal (max (-(T θ)) 0) ≤ ‖T θ‖₊ := by
      intro θ
      rw [hofmaxR (-(T θ)),
        show (‖T θ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖T θ‖ from ENNReal.ofReal_coe_nnreal.symm]
      exact ENNReal.ofReal_le_ofReal (by
        rw [Real.norm_eq_abs]
        exact neg_le_abs (T θ))
    exact lt_of_le_of_lt (lintegral_mono hb) hTint.2
  have hGnegfin : (∫⁻ θ, ENNReal.ofReal (-(G θ)) ∂(calQ : Measure Θ)) ≠ ⊤ := by
    have hb : ∀ θ : Θ, ENNReal.ofReal (-(G θ))
        ≤ ENNReal.ofReal (max (T θ - G θ) 0) + ENNReal.ofReal (max (-(T θ)) 0) := by
      intro θ
      have hpt : -(G θ) ≤ max (T θ - G θ) 0 + max (-(T θ)) 0 := by
        have h1 : T θ - G θ ≤ max (T θ - G θ) 0 := le_max_left _ _
        have h2 : -(T θ) ≤ max (-(T θ)) 0 := le_max_left _ _
        linarith
      calc ENNReal.ofReal (-(G θ))
          ≤ ENNReal.ofReal (max (T θ - G θ) 0 + max (-(T θ)) 0) := ENNReal.ofReal_le_ofReal hpt
        _ ≤ ENNReal.ofReal (max (T θ - G θ) 0) + ENNReal.ofReal (max (-(T θ)) 0) :=
            ENNReal.ofReal_add_le
    have hsum : (∫⁻ θ, (ENNReal.ofReal (max (T θ - G θ) 0)
        + ENNReal.ofReal (max (-(T θ)) 0)) ∂(calQ : Measure Θ)) < ⊤ := by
      have hsplit : (∫⁻ θ, (ENNReal.ofReal (max (T θ - G θ) 0)
          + ENNReal.ofReal (max (-(T θ)) 0)) ∂(calQ : Measure Θ))
          = (∫⁻ θ, ENNReal.ofReal (max (T θ - G θ) 0) ∂(calQ : Measure Θ))
            + (∫⁻ θ, ENNReal.ofReal (max (-(T θ)) 0) ∂(calQ : Measure Θ)) := by
        show (∫⁻ θ, (ENNReal.ofReal ∘ fun θ : Θ => max (T θ - G θ) 0) θ
          + (ENNReal.ofReal ∘ fun θ : Θ => max (-(T θ)) 0) θ ∂(calQ : Measure Θ)) = _
        rw [lintegral_add_left (ENNReal.measurable_ofReal.comp hMTG)]
        simp only [Function.comp_apply]
      rw [hsplit, ENNReal.add_lt_top]
      exact ⟨lt_of_le_of_ne le_top hM1, hTnegfin⟩
    exact ne_of_lt (lt_of_le_of_lt (lintegral_mono hb) hsum)
  have hGEr : (∫⁻ θ, ENNReal.ofReal (max (GE θ) 0) ∂(calQ : Measure Θ)) < ⊤ := by
    have hb : ∀ θ : Θ, ENNReal.ofReal (max (GE θ) 0) ≤ ‖GE θ‖₊ := by
      intro θ
      rw [hofmaxR (GE θ),
        show (‖GE θ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖GE θ‖ from ENNReal.ofReal_coe_nnreal.symm]
      exact ENNReal.ofReal_le_ofReal (by
        rw [Real.norm_eq_abs]
        exact le_abs_self (GE θ))
    exact lt_of_le_of_lt (lintegral_mono hb) hGEint.2
  have hCnegfin :
      (∫⁻ θ, ENNReal.ofReal (max (-(G θ - GE θ)) 0) ∂(calQ : Measure Θ)) < ⊤ := by
    have hb : ∀ θ : Θ, ENNReal.ofReal (max (-(G θ - GE θ)) 0)
        ≤ ENNReal.ofReal (max (-(G θ)) 0) + ENNReal.ofReal (max (GE θ) 0) := by
      intro θ
      have hpt : max (-(G θ - GE θ)) 0 ≤ max (-(G θ)) 0 + max (GE θ) 0 := by
        have h1 : -(G θ - GE θ) ≤ max (-(G θ)) 0 + max (GE θ) 0 := by
          have h2 : -(G θ) ≤ max (-(G θ)) 0 := le_max_left _ _
          have h3 : GE θ ≤ max (GE θ) 0 := le_max_left _ _
          linarith
        refine max_le h1 ?_
        have h2 : (0 : ℝ) ≤ max (-(G θ)) 0 := le_max_right _ _
        have h3 : (0 : ℝ) ≤ max (GE θ) 0 := le_max_right _ _
        linarith
      calc ENNReal.ofReal (max (-(G θ - GE θ)) 0)
          ≤ ENNReal.ofReal (max (-(G θ)) 0 + max (GE θ) 0) := ENNReal.ofReal_le_ofReal hpt
        _ ≤ ENNReal.ofReal (max (-(G θ)) 0) + ENNReal.ofReal (max (GE θ) 0) :=
            ENNReal.ofReal_add_le
    have hsum : (∫⁻ θ, (ENNReal.ofReal (max (-(G θ)) 0)
        + ENNReal.ofReal (max (GE θ) 0)) ∂(calQ : Measure Θ)) < ⊤ := by
      have hsplit : (∫⁻ θ, (ENNReal.ofReal (max (-(G θ)) 0)
          + ENNReal.ofReal (max (GE θ) 0)) ∂(calQ : Measure Θ))
          = (∫⁻ θ, ENNReal.ofReal (max (-(G θ)) 0) ∂(calQ : Measure Θ))
            + (∫⁻ θ, ENNReal.ofReal (max (GE θ) 0) ∂(calQ : Measure Θ)) := by
        show (∫⁻ θ, (ENNReal.ofReal ∘ fun θ : Θ => max (-(G θ)) 0) θ
          + (ENNReal.ofReal ∘ fun θ : Θ => max (GE θ) 0) θ ∂(calQ : Measure Θ)) = _
        rw [lintegral_add_left
          (ENNReal.measurable_ofReal.comp (hMG.neg.max measurable_const))]
        simp only [Function.comp_apply]
      rw [hsplit, ENNReal.add_lt_top]
      refine ⟨?_, hGEr⟩
      rw [lintegral_congr fun θ => hofmaxR (-(G θ))]
      exact lt_of_le_of_ne le_top hGnegfin
    exact lt_of_le_of_lt (lintegral_mono hb) hsum
  have hMGE : Measurable GE :=
    statopia_math_node_4065279287_e9ac2bcb M hEll n hn omega hPost_meas hL_int hLgibbsEmp_int
  have hφnegfin : (∫⁻ x, ENNReal.ofReal (-(phi x)) ∂nu) ≠ ⊤ := by
    have hfib : ∀ θ : Θ, Integrable (fun u : Fin n → U => phi (θ, u))
          (Measure.pi fun i : Fin n =>
            (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)) ∧
        ((∫ u, phi (θ, u) ∂(Measure.pi fun i : Fin n =>
              (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))) = G θ - GE θ) :=
      hFub.1
    have hTonP : (∫⁻ x, ENNReal.ofReal (phi x) ∂nu) = ∫⁻ θ,
        (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
          (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))) ∂(calQ : Measure Θ) :=
      hFub.2.1
    have hTonN : (∫⁻ x, ENNReal.ofReal (-(phi x)) ∂nu) = ∫⁻ θ,
        (∫⁻ u, ENNReal.ofReal (-(phi (θ, u))) ∂(Measure.pi fun i : Fin n =>
          (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))) ∂(calQ : Measure Θ) :=
      hFub.2.2.1
    have hrot : ∀ x y z : ℝ≥0∞, x + (y + z) = y + (z + x) := by
      intro x y z
      rw [add_comm x (y + z), add_assoc]
    have hpt : ∀ θ : Θ,
        (∫⁻ u, ENNReal.ofReal (-(phi (θ, u))) ∂(Measure.pi fun i : Fin n =>
            (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))
          ≤ ENNReal.ofReal (max (-(G θ)) 0)
            + (ENNReal.ofReal (max (GE θ) 0)
              + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))) := by
      intro θ
      obtain ⟨hintθ, hvalθ⟩ := hfib θ
      have hane : (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
            (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))) ≠ ⊤ := by
        have hb : ∀ u : Fin n → U, ENNReal.ofReal (phi (θ, u)) ≤ ‖phi (θ, u)‖₊ := by
          intro u
          rw [show (‖phi (θ, u)‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖phi (θ, u)‖ from
            ENNReal.ofReal_coe_nnreal.symm]
          exact ENNReal.ofReal_le_ofReal (by
            rw [Real.norm_eq_abs]
            exact le_abs_self (phi (θ, u)))
        exact ne_of_lt (lt_of_le_of_lt (lintegral_mono hb) hintθ.2)
      have hbne : (∫⁻ u, ENNReal.ofReal (-(phi (θ, u))) ∂(Measure.pi fun i : Fin n =>
            (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))) ≠ ⊤ := by
        have hb : ∀ u : Fin n → U, ENNReal.ofReal (-(phi (θ, u))) ≤ ‖phi (θ, u)‖₊ := by
          intro u
          rw [show (‖phi (θ, u)‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖phi (θ, u)‖ from
            ENNReal.ofReal_coe_nnreal.symm]
          exact ENNReal.ofReal_le_ofReal (by
            rw [Real.norm_eq_abs]
            exact neg_le_abs (phi (θ, u)))
        exact ne_of_lt (lt_of_le_of_lt (lintegral_mono hb) hintθ.2)
      have hdec := MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hintθ
      have hCeq : (∫⁻ u, ENNReal.ofReal (-(phi (θ, u))) ∂(Measure.pi fun i : Fin n =>
            (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))).toReal
          = (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
              (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))).toReal
            + (-(G θ - GE θ)) := by
        have h1 := hdec
        rw [hvalθ] at h1
        linarith
      have hCb : ENNReal.ofReal (-(G θ - GE θ))
          ≤ ENNReal.ofReal (max (-(G θ)) 0) + ENNReal.ofReal (max (GE θ) 0) := by
        rw [← hofmaxR (-(G θ - GE θ))]
        have h1 : -(G θ - GE θ) ≤ max (-(G θ)) 0 + max (GE θ) 0 := by
          have h2 : -(G θ) ≤ max (-(G θ)) 0 := le_max_left _ _
          have h3 : GE θ ≤ max (GE θ) 0 := le_max_left _ _
          linarith
        have h2 : (0 : ℝ) ≤ max (-(G θ)) 0 := le_max_right _ _
        have h3 : (0 : ℝ) ≤ max (GE θ) 0 := le_max_right _ _
        calc ENNReal.ofReal (max (-(G θ - GE θ)) 0)
            ≤ ENNReal.ofReal (max (-(G θ)) 0 + max (GE θ) 0) :=
              ENNReal.ofReal_le_ofReal (max_le h1 (by linarith))
          _ ≤ ENNReal.ofReal (max (-(G θ)) 0) + ENNReal.ofReal (max (GE θ) 0) :=
              ENNReal.ofReal_add_le
      calc (∫⁻ u, ENNReal.ofReal (-(phi (θ, u))) ∂(Measure.pi fun i : Fin n =>
              (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))
          = ENNReal.ofReal ((∫⁻ u, ENNReal.ofReal (-(phi (θ, u)))
                ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))).toReal) :=
            (ENNReal.ofReal_toReal hbne).symm
        _ = ENNReal.ofReal ((∫⁻ u, ENNReal.ofReal (phi (θ, u))
                ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))).toReal
              + (-(G θ - GE θ))) := by rw [hCeq]
        _ ≤ ENNReal.ofReal ((∫⁻ u, ENNReal.ofReal (phi (θ, u))
                ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))).toReal)
              + ENNReal.ofReal (-(G θ - GE θ)) := ENNReal.ofReal_add_le
        _ ≤ ENNReal.ofReal ((∫⁻ u, ENNReal.ofReal (phi (θ, u))
                ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))).toReal)
              + (ENNReal.ofReal (max (-(G θ)) 0) + ENNReal.ofReal (max (GE θ) 0)) :=
            add_le_add le_rfl hCb
        _ = ENNReal.ofReal (max (-(G θ)) 0)
              + (ENNReal.ofReal (max (GE θ) 0)
                + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
                    (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))) := by
            rw [ENNReal.ofReal_toReal hane]
            exact hrot _ _ _
    have hAfin : (∫⁻ θ, ENNReal.ofReal (max (-(G θ)) 0) ∂(calQ : Measure Θ)) < ⊤ := by
      rw [lintegral_congr fun θ => hofmaxR (-(G θ))]
      exact lt_of_le_of_ne le_top hGnegfin
    have hafin : (∫⁻ θ, (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
          (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))) ∂(calQ : Measure Θ)) < ⊤ := by
      rw [← hTonP]
      exact lt_of_le_of_ne le_top hφposfin
    have hfin2 : (∫⁻ θ, (ENNReal.ofReal (max (GE θ) 0)
        + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
            (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))) ∂(calQ : Measure Θ)) < ⊤ := by
      have hsplit : (∫⁻ θ, (ENNReal.ofReal (max (GE θ) 0)
          + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
              (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))) ∂(calQ : Measure Θ))
          = (∫⁻ θ, ENNReal.ofReal (max (GE θ) 0) ∂(calQ : Measure Θ))
            + (∫⁻ θ, (∫⁻ u, ENNReal.ofReal (phi (θ, u))
                ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))
                ∂(calQ : Measure Θ)) := by
        show (∫⁻ θ, (ENNReal.ofReal ∘ fun θ : Θ => max (GE θ) 0) θ
          + (fun θ : Θ => ∫⁻ u, ENNReal.ofReal (phi (θ, u))
              ∂(Measure.pi fun i : Fin n =>
                (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))) θ
              ∂(calQ : Measure Θ)) = _
        rw [lintegral_add_left (ENNReal.measurable_ofReal.comp (hMGE.max measurable_const))]
        simp only [Function.comp_apply]
      rw [hsplit, ENNReal.add_lt_top]
      exact ⟨hGEr, hafin⟩
    have hfin1 : (∫⁻ θ, (ENNReal.ofReal (max (-(G θ)) 0)
        + (ENNReal.ofReal (max (GE θ) 0)
          + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
              (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))))) ∂(calQ : Measure Θ)) < ⊤ := by
      have hsplit : (∫⁻ θ, (ENNReal.ofReal (max (-(G θ)) 0)
          + (ENNReal.ofReal (max (GE θ) 0)
            + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
                (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))))) ∂(calQ : Measure Θ))
          = (∫⁻ θ, ENNReal.ofReal (max (-(G θ)) 0) ∂(calQ : Measure Θ))
            + (∫⁻ θ, (ENNReal.ofReal (max (GE θ) 0)
              + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U))))
              ∂(calQ : Measure Θ)) := by
        show (∫⁻ θ, (ENNReal.ofReal ∘ fun θ : Θ => max (-(G θ)) 0) θ
          + (fun θ : Θ => ENNReal.ofReal (max (GE θ) 0)
              + (∫⁻ u, ENNReal.ofReal (phi (θ, u)) ∂(Measure.pi fun i : Fin n =>
                  (basePost M ((mOf omega i : ℕ)) (SOF omega i) θ : Measure U)))) θ
              ∂(calQ : Measure Θ)) = _
        rw [lintegral_add_left
          (ENNReal.measurable_ofReal.comp (hMG.neg.max measurable_const))]
        simp only [Function.comp_apply]
      rw [hsplit, ENNReal.add_lt_top]
      exact ⟨hAfin, hfin2⟩
    rw [hTonN]
    exact ne_of_lt (lt_of_le_of_lt (lintegral_mono hpt) hfin1)
  have hφint : Integrable phi nu := by
    have habs : ∀ x : Θ × (Fin n → U),
        ‖phi x‖₊ = ENNReal.ofReal (phi x) + ENNReal.ofReal (-(phi x)) := by
      intro x
      have h2 : (‖phi x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖phi x‖ := ENNReal.ofReal_coe_nnreal.symm
      have hmax : ‖phi x‖ = max (phi x) 0 + max (-(phi x)) 0 := by
        rcases le_total 0 (phi x) with h | h
        · rw [max_eq_left h, max_eq_right (by linarith : -(phi x) ≤ 0), Real.norm_eq_abs,
            abs_of_nonneg h]
          ring
        · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -(phi x)), Real.norm_eq_abs,
            abs_of_nonpos h]
          ring
      rw [h2, hmax, ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
        hofmaxR (phi x), hofmaxR (-(phi x))]
    have hfin : (∫⁻ x, ‖phi x‖₊ ∂nu) < ⊤ := by
      have hsplit : (∫⁻ x, ‖phi x‖₊ ∂nu)
          = (∫⁻ x, ENNReal.ofReal (phi x) ∂nu) + (∫⁻ x, ENNReal.ofReal (-(phi x)) ∂nu) := by
        rw [lintegral_congr habs]
        show (∫⁻ x, (ENNReal.ofReal ∘ phi) x
          + (ENNReal.ofReal ∘ fun y : Θ × (Fin n → U) => -(phi y)) x ∂nu) = _
        rw [lintegral_add_left (ENNReal.measurable_ofReal.comp hφmeas)]
        simp only [Function.comp_apply]
      rw [hsplit, ENNReal.add_lt_top]
      exact ⟨lt_of_le_of_ne le_top hφposfin, lt_of_le_of_ne le_top hφnegfin⟩
    exact ⟨hφmeas.aestronglyMeasurable, hfin⟩
  have hGint : Integrable G (calQ : Measure Θ) := by
    have hdiff : Integrable (fun θ : Θ => G θ - GE θ) (calQ : Measure Θ) :=
      (hFub.2.2.2.2.2 hφint).1
    have hsum : Integrable (fun θ : Θ => GE θ + (G θ - GE θ)) (calQ : Measure Θ) :=
      hGEint.add hdiff
    exact hsum.congr (Filter.Eventually.of_forall fun θ => by ring)
  exact ⟨hGint, hφint⟩
  /- @proof-region region.target-node.session.78b19b16c8486232 end -/

end
end Statlib.Imported
