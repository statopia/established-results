import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_2469337524_a68c5ec1_5bdd031d
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_2526795459_802d95db_38e28795
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4000542074_30367f47_51acbb0f
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
theorem statopia_math_node_3842740502_61a3134f : ∀ {X Y U Θ V : Type*}
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
    (hPrior_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ => basePrior M k q.1 q.2)
    (hPost_meas : ∀ k : ℕ, Measurable fun q : (Fin k → X × Y) × Θ => basePost M k q.1 q.2)
    (hKL_meas : ∀ (k : ℕ) (S : Fin k → X × Y), Measurable fun θ : Θ =>
      InformationTheory.klDiv (basePost M k S θ : Measure U) (basePrior M k S θ : Measure U))
    (hℓ_int : ∀ (u : U) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun z : X × Y => M.ℓ u z) (D : Measure (X × Y)))
    (hLgibbs_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ) (D : ProbabilityMeasure (X × Y)),
      Integrable (fun u : U => Lmean M.ℓ u (D : Measure (X × Y))) (basePost M k S θ : Measure U))
    (hLgibbsEmp_int : ∀ (k : ℕ) (S : Fin k → X × Y) (θ : Θ),
      Integrable (fun u : U => Lemp M.ℓ u S) (basePost M k S θ : Measure U))
    (hTransferLoss_int : ∀ 𝒬 : ProbabilityMeasure Θ,
      Integrable (fun θ : Θ =>
        ∫ p, transferAt M θ p ∂(𝒯 : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
        (𝒬 : Measure Θ))
    (hEmpMulti_int : ∀ (𝒬 : ProbabilityMeasure Θ) (ω : Fin n → Block (X × Y)),
      Integrable (fun θ : Θ => (1 / (n : ℝ)) * ∑ i : Fin n,
        LgibbsEmp M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (SOF ω i))
        (𝒬 : Measure Θ))
    (hPi1Exp_int : ∀ (ω : Fin n → Block (X × Y)) (θ : Θ),
      Integrable (Pi1Exp M n gam ω θ)
        (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)))
    (hPi1Inner_int : ∀ ω : Fin n → Block (X × Y),
      Integrable (fun θ : Θ => Pi1Inner M n gam ω θ) (HP : Measure Θ))
    (hPi2Exp_int : ∀ ω : Fin n → Block (X × Y),
      Integrable (fun θ : Θ => Pi2Exp M n 𝒯 lam ω θ) (HP : Measure Θ))
    (ω : Fin n → Block (X × Y)) (𝒬 : ProbabilityMeasure Θ),
    (transferLoss M 𝒬 𝒯 : EReal) ≤
      (empMulti M n 𝒬 ω : EReal)
      + ((((1 : ℝ) / lam + 1 / gam) : ℝ) : EReal)
          * (ENNReal.toEReal
              (InformationTheory.klDiv (𝒬 : Measure Θ) (HP : Measure Θ)))
      + ((((1 : ℝ) / gam) : ℝ) : EReal) * baseKLSum M n 𝒬 ω
      + (Pi1 M n HP gam ω : EReal) + (Pi2 M n 𝒯 HP lam ω : EReal) := by
  /- @proof-region region.target-node.session.c5d174388277d0fc begin -/
  intro X Y U Θ V
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro M hloss HP lam gam hlam hgam n hn Ttask hPrior_meas hPost_meas hKL_meas
    hloss_int hLgibbs_int hLgibbsEmp_int hTransferLoss_int hEmpMulti_int
    hPi1Exp_int hPi1Inner_int hPi2Exp_int ω Qpost
  have hcore : ((transferLoss M Qpost Ttask : EReal) - (empMulti M n Qpost ω : EReal))
      ≤ (((1 : ℝ) / lam + 1 / gam) : EReal)
          * (ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)))
        + (((1 : ℝ) / gam) : EReal) * baseKLSum M n Qpost ω
        + (Pi1 M n HP gam ω : EReal)
        + (Pi2 M n Ttask HP lam ω : EReal) := by
    have hexp2 : ∀ θ : Θ, Pi2Exp M n Ttask lam ω θ
        = Real.exp (lam * ((∫ p,
              transferAt M θ p ∂(Ttask : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
            - (1 / (n : ℝ)) * ∑ i : Fin n,
                Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
                  (DOf ω i : Measure (X × Y)))) := by
      intro θ
      simp only [Pi2Exp]
      congr 1
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hexp1 : ∀ (θ : Θ) (u : Fin n → U), Pi1Exp M n gam ω θ u
        = Real.exp (gam * ((1 / (n : ℝ)) * ∑ i : Fin n,
            (Lmean M.ℓ (u i) (DOf ω i : Measure (X × Y))
              - Lemp M.ℓ (u i) (SOF ω i)))) := by
      intro θ u
      simp only [Pi1Exp, Lemp, SOF]
      congr 1
      have hterm : ∀ i : Fin n,
          (1 / ((mOf ω i : ℕ) : ℝ))
              * ∑ j : Fin ((mOf ω i : ℕ)),
                (Lmean M.ℓ (u i) (DOf ω i : Measure (X × Y)) - M.ℓ (u i) ((ω i).2 j))
            = Lmean M.ℓ (u i) (DOf ω i : Measure (X × Y))
              - 1 / ((mOf ω i : ℕ) : ℝ)
                * ∑ j : Fin ((mOf ω i : ℕ)), M.ℓ (u i) ((ω i).2 j) := by
        intro i
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hm : ((mOf ω i : ℕ) : ℝ) ≠ 0 := by
          have h := (mOf ω i).pos
          exact_mod_cast h.ne'
        field_simp
      have hsum : ∑ i : Fin n,
            (1 / ((mOf ω i : ℕ) : ℝ))
              * ∑ j : Fin ((mOf ω i : ℕ)),
                (Lmean M.ℓ (u i) (DOf ω i : Measure (X × Y)) - M.ℓ (u i) ((ω i).2 j))
          = ∑ i : Fin n,
              (Lmean M.ℓ (u i) (DOf ω i : Measure (X × Y))
                - 1 / ((mOf ω i : ℕ) : ℝ)
                  * ∑ j : Fin ((mOf ω i : ℕ)), M.ℓ (u i) ((ω i).2 j)) :=
        Finset.sum_congr rfl fun i _ => hterm i
      rw [hsum, Finset.sum_sub_distrib]
      ring
    let ψ : Θ → ℝ := fun θ =>
      (∫ p, transferAt M θ p ∂(Ttask : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
        - (1 / (n : ℝ)) * ∑ i : Fin n,
            Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)
              (DOf ω i : Measure (X × Y))
    have hψ_exp : ∀ θ : Θ, Real.exp (lam * ψ θ) = Pi2Exp M n Ttask lam ω θ :=
      fun θ => (hexp2 θ).symm
    let φ : Θ × (Fin n → U) → ℝ := fun x =>
      (1 / (n : ℝ)) * ∑ i : Fin n,
        (Lmean M.ℓ (x.2 i) (DOf ω i : Measure (X × Y))
          - Lemp M.ℓ (x.2 i) (SOF ω i))
    have hφ_exp : ∀ x : Θ × (Fin n → U), Real.exp (gam * φ x) = Pi1Exp M n gam ω x.1 x.2 :=
      fun x => (hexp1 x.1 x.2).symm
    have hcoe_meas : Measurable fun p : ProbabilityMeasure U => (p : Measure U) :=
      measurable_subtype_coe
    have hmeas_prior : ∀ i : Fin n, Measurable fun θ : Θ =>
        (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) := by
      intro i
      have hpair : Measurable fun θ : Θ => (SOF ω i, θ) :=
        measurable_const.prodMk measurable_id
      exact hcoe_meas.comp ((hPrior_meas ((mOf ω i : ℕ))).comp hpair)
    have hmeas_post : ∀ i : Fin n, Measurable fun θ : Θ =>
        (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) := by
      intro i
      have hpair : Measurable fun θ : Θ => (SOF ω i, θ) :=
        measurable_const.prodMk measurable_id
      exact hcoe_meas.comp ((hPost_meas ((mOf ω i : ℕ))).comp hpair)
    have hKLchain : ENNReal.toEReal
        (InformationTheory.klDiv
          ((Qpost : Measure Θ).bind fun θ =>
            (Measure.pi fun i : Fin n =>
              (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
              (fun u : Fin n → U => (θ, u)))
          ((HP : Measure Θ).bind fun θ =>
            (Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
              (fun u : Fin n → U => (θ, u))))
        = ENNReal.toEReal
            (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
          + baseKLSum M n Qpost ω :=
      statopia_math_node_2526795459_802d95db M HP Qpost n hn ω hmeas_prior hmeas_post
        (fun i => hKL_meas ((mOf ω i : ℕ)) (SOF ω i))
    have hψ_rep : ∃ ψ' : Θ → ℝ, Measurable ψ' ∧ ψ' =ᵐ[(HP : Measure Θ)] ψ := by
      have hae : AEStronglyMeasurable (fun θ : Θ => Pi2Exp M n Ttask lam ω θ)
          (HP : Measure Θ) := (hPi2Exp_int ω).aestronglyMeasurable
      obtain ⟨g, hg_sm, hg_ae⟩ := hae
      have hg_meas : Measurable g := hg_sm.measurable
      refine ⟨fun θ => (1 / lam) * Real.log (g θ),
        (Real.measurable_log.comp hg_meas).const_mul _, ?_⟩
      filter_upwards [hg_ae] with θ hθ
      have h2 : Real.exp (lam * ψ θ) = g θ := (hψ_exp θ).trans hθ
      have h3 : Real.log (g θ) = lam * ψ θ := by
        rw [← h2, Real.log_exp]
      rw [h3]
      field_simp
    obtain ⟨ψ', hψ'_meas, hψ'_ae⟩ := hψ_rep
    have hExpψ' : Integrable (fun θ : Θ => Real.exp (lam * ψ' θ)) (HP : Measure Θ) := by
      refine (hPi2Exp_int ω).congr ?_
      filter_upwards [hψ'_ae] with θ hθ
      rw [hθ]
      exact (hψ_exp θ).symm
    have hmeta_engine :=
      statopia_math_node_4000542074_30367f47 HP Qpost lam hlam ψ' hψ'_meas hExpψ'
    have hlogeq : (∫ x : Θ, Real.exp (lam * ψ' x) ∂(HP : Measure Θ))
        = ∫ x : Θ, Pi2Exp M n Ttask lam ω x ∂(HP : Measure Θ) := by
      refine integral_congr_ae ?_
      filter_upwards [hψ'_ae] with x hx
      rw [hx]
      exact hψ_exp x
    have hmeta_form : ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (ψ' x) ∂(Qpost : Measure Θ))
        ≤ ((lam⁻¹ : ℝ) : EReal)
            * (ENNReal.toEReal
                (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
              + (Real.log (∫ x : Θ, Pi2Exp M n Ttask lam ω x ∂(HP : Measure Θ)) : EReal))
          + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(ψ' x)) ∂(Qpost : Measure Θ)) := by
      have h := hmeta_engine
      rw [hlogeq] at h
      exact h
    have hmeta_Q : ∀ (hQ : ψ' =ᵐ[(Qpost : Measure Θ)] ψ),
        ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (ψ x) ∂(Qpost : Measure Θ))
          ≤ ((lam⁻¹ : ℝ) : EReal)
              * (ENNReal.toEReal
                  (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
                + (Real.log (∫ x : Θ, Pi2Exp M n Ttask lam ω x ∂(HP : Measure Θ)) : EReal))
            + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(ψ x)) ∂(Qpost : Measure Θ)) := by
      intro hQ
      have h1 : (∫⁻ x, ENNReal.ofReal (ψ' x) ∂(Qpost : Measure Θ))
          = ∫⁻ x, ENNReal.ofReal (ψ x) ∂(Qpost : Measure Θ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hQ] with x hx
        rw [hx]
      have h2 : (∫⁻ x, ENNReal.ofReal (-(ψ' x)) ∂(Qpost : Measure Θ))
          = ∫⁻ x, ENNReal.ofReal (-(ψ x)) ∂(Qpost : Measure Θ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hQ] with x hx
        rw [hx]
      rw [h1, h2] at hmeta_form
      exact hmeta_form
    have htricho : ∀ x : EReal, x = ⊥ ∨ x = ⊤ ∨ ∃ r : ℝ, x = ↑r := by
      intro x
      rcases x with _ | x
      · exact Or.inl rfl
      · rcases x with _ | x
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨x, rfl⟩)
    have hmerge_coe : ∀ (a b r : ℝ),
        (a : EReal) * (r : EReal) + (b : EReal) * (r : EReal)
          = ((a + b : ℝ) : EReal) * (r : EReal) := by
      intro a b r
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        show a * r + b * r = (a + b) * r by ring]
    have hψ'_ae_Q : ∀ (hac : (Qpost : Measure Θ) ≪ (HP : Measure Θ)),
        ψ' =ᵐ[(Qpost : Measure Θ)] ψ := by
      intro hac
      refine (MeasureTheory.ae_iff (μ := (Qpost : Measure Θ))
        (p := fun x : Θ => ψ' x = ψ x)).2 ?_
      exact hac ((MeasureTheory.ae_iff (μ := (HP : Measure Θ))
        (p := fun x : Θ => ψ' x = ψ x)).1 hψ'_ae)
    have hmeta_ac : (Qpost : Measure Θ) ≪ (HP : Measure Θ) →
        ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (ψ x) ∂(Qpost : Measure Θ))
          ≤ ((lam⁻¹ : ℝ) : EReal)
              * (ENNReal.toEReal
                  (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
                + (Real.log (∫ x : Θ, Pi2Exp M n Ttask lam ω x ∂(HP : Measure Θ)) : EReal))
            + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(ψ x)) ∂(Qpost : Measure Θ)) :=
      fun hac => hmeta_Q (hψ'_ae_Q hac)
    have hcoe_coef : ((((1 : ℝ) / lam + 1 / gam : ℝ)) : EReal)
        = ((lam⁻¹ : ℝ) : EReal) + ((gam⁻¹ : ℝ) : EReal) := by
      rw [EReal.coe_add, one_div, one_div]
    have hexpψ_int : (∫ x : Θ, Real.exp (lam * ψ x) ∂(HP : Measure Θ))
        = ∫ x : Θ, Pi2Exp M n Ttask lam ω x ∂(HP : Measure Θ) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      exact hψ_exp x
    have hPi1Inner_eq : ∀ θ : Θ, Pi1Inner M n gam ω θ
        = ∫ u : Fin n → U, Real.exp (gam * φ (θ, u))
            ∂(Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) := by
      intro θ
      rw [Pi1Inner]
      refine integral_congr_ae ?_
      filter_upwards with u
      exact (hφ_exp (θ, u)).symm
    let ν : Measure (Θ × (Fin n → U)) := (Qpost : Measure Θ).bind fun θ =>
      (Measure.pi fun i : Fin n =>
        (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map (fun u => (θ, u))
    let μ : Measure (Θ × (Fin n → U)) := (HP : Measure Θ).bind fun θ =>
      (Measure.pi fun i : Fin n =>
        (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map (fun u => (θ, u))
    have hKLchain' : ENNReal.toEReal (InformationTheory.klDiv ν μ)
        = ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
          + baseKLSum M n Qpost ω := hKLchain
    have hPi1_def : Pi1 M n HP gam ω
        = (1 / gam) * Real.log (∫ x : Θ, Pi1Inner M n gam ω x ∂(HP : Measure Θ)) := rfl
    have hPi2_def : Pi2 M n Ttask HP lam ω
        = (1 / lam) * Real.log (∫ x : Θ, Pi2Exp M n Ttask lam ω x ∂(HP : Measure Θ)) := rfl
    have hlog_pi1 : Real.log (∫ x : Θ, Pi1Inner M n gam ω x ∂(HP : Measure Θ))
        = gam * Pi1 M n HP gam ω := by
      have hg : gam ≠ 0 := ne_of_gt hgam
      rw [hPi1_def]
      field_simp
    have hlog_pi2 : Real.log (∫ x : Θ, Pi2Exp M n Ttask lam ω x ∂(HP : Measure Θ))
        = lam * Pi2 M n Ttask HP lam ω := by
      have hl : lam ≠ 0 := ne_of_gt hlam
      rw [hPi2_def]
      field_simp
    have hreal_combo : ∀ (a b l k β q1 q2 : ℝ),
        l - b ≤ q1 + gam⁻¹ * k + gam⁻¹ * β →
        a - l ≤ q2 + lam⁻¹ * k →
        a - b ≤ (lam⁻¹ + gam⁻¹) * k + gam⁻¹ * β + q1 + q2 := by
      intro a b l k β q1 q2 h1 h2
      linarith
    have hfib_int : ∀ θ : Θ,
        Integrable (fun u : Fin n → U => Real.exp (gam * φ (θ, u)))
          (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) := by
      intro θ
      refine (hPi1Exp_int ω θ).congr ?_
      filter_upwards with u
      exact (hφ_exp (θ, u)).symm
    have hExpψ : Integrable (fun θ : Θ => Real.exp (lam * ψ θ)) (HP : Measure Θ) := by
      refine (hPi2Exp_int ω).congr ?_
      filter_upwards with θ
      exact (hψ_exp θ).symm
    have hcoe_le : ∀ {a b : ℝ}, a ≤ b → ((a : EReal) ≤ (b : EReal)) := by
      intro a b h
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)
    have hcoe_le' : ∀ {a b : ℝ}, ((a : EReal) ≤ (b : EReal)) → a ≤ b := by
      intro a b h
      exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h)
    have hcoe_ne_top : ∀ r : ℝ, ((r : EReal)) ≠ ⊤ := by
      intro r h
      have h' : (↑r : WithTop ℝ) = ⊤ := WithBot.coe_injective h
      exact WithTop.coe_ne_top h'
    have hcoe_ne_bot : ∀ r : ℝ, ((r : EReal)) ≠ ⊥ := by
      intro r h
      exact WithBot.coe_ne_bot h
    have hnot_top_le_coe : ∀ r : ℝ, ¬ ((⊤ : EReal) ≤ ((r : EReal))) := by
      intro r h
      exact hcoe_ne_top r (le_antisymm h le_top).symm
    have hne_top_of_le_coe : ∀ (x : EReal) (r : ℝ), x ≤ ((r : EReal)) → x ≠ ⊤ := by
      intro x r h hx
      rw [hx] at h
      exact hnot_top_le_coe r h
    have hsub_add_coe : ∀ (x : EReal) (r : ℝ),
        x - ((r : EReal)) + ((r : EReal)) = x := by
      intro x r
      rcases htricho x with h | h | ⟨s, hs⟩
      · rw [h]
        simp
      · rw [h]
        simp
      · rw [hs, ← EReal.coe_sub, ← EReal.coe_add, sub_add_cancel]
    have hadd_sub_coe : ∀ (x : EReal) (r : ℝ),
        x + ((r : EReal)) - ((r : EReal)) = x := by
      intro x r
      rcases htricho x with h | h | ⟨s, hs⟩
      · rw [h]
        simp
      · rw [h]
        simp
      · rw [hs, ← EReal.coe_add, ← EReal.coe_sub]
        congr 1
        ring
    have hadd_top : ∀ r : ℝ, (((r : EReal)) + ⊤ : EReal) = ⊤ := by
      intro r
      simp
    have htop_add : ∀ r : ℝ, ((⊤ : EReal) + ((r : EReal))) = ⊤ := by
      intro r
      simp
    have hsub_top : ∀ r : ℝ, ((⊤ : EReal) - ((r : EReal))) = ⊤ := by
      intro r
      simp
    have hsub_bot : ∀ r : ℝ, (((r : EReal)) - (⊥ : EReal)) = ⊤ := by
      intro r
      simp
    have hcombo : ∀ (tL eM l k β q1 q2 : ℝ),
        ((l : EReal)) - ((eM : EReal))
          ≤ ((gam⁻¹ : ℝ) : EReal) * ((k : EReal))
            + ((gam⁻¹ : ℝ) : EReal) * ((β : EReal)) + ((q1 : EReal)) →
        ((tL : EReal)) - ((l : EReal))
          ≤ ((lam⁻¹ : ℝ) : EReal) * ((k : EReal)) + ((q2 : EReal)) →
        ((tL : EReal)) - ((eM : EReal))
          ≤ ((((1 : ℝ) / lam + 1 / gam) : ℝ) : EReal) * ((k : EReal))
            + ((gam⁻¹ : ℝ) : EReal) * ((β : EReal))
            + ((q1 : EReal)) + ((q2 : EReal)) := by
      intro tL eM l k β q1 q2 h1 h2
      have h1r : l - eM ≤ gam⁻¹ * k + gam⁻¹ * β + q1 := by
        have h := h1
        rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
          ← EReal.coe_add] at h
        exact hcoe_le' h
      have h2r : tL - l ≤ lam⁻¹ * k + q2 := by
        have h := h2
        rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add] at h
        exact hcoe_le' h
      have hreal : tL - eM ≤ (lam⁻¹ + gam⁻¹) * k + gam⁻¹ * β + q1 + q2 := by
        linarith
      have hlhs : ((tL : EReal)) - ((eM : EReal)) = (((tL - eM : ℝ)) : EReal) := by
        rw [EReal.coe_sub]
      have hrhs : ((((1 : ℝ) / lam + 1 / gam) : ℝ) : EReal) * ((k : EReal))
            + ((gam⁻¹ : ℝ) : EReal) * ((β : EReal)) + ((q1 : EReal)) + ((q2 : EReal))
          = ((((lam⁻¹ + gam⁻¹) * k + gam⁻¹ * β + q1 + q2 : ℝ)) : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
          ← EReal.coe_add]
        congr 1
        ring
      rw [hlhs, hrhs]
      exact hcoe_le hreal
    have hbundled : ∀ (l eM k β q1 : ℝ),
        ((l : EReal)) - ((eM : EReal))
            ≤ ((gam⁻¹ : ℝ) : EReal)
              * (((k : EReal)) + ((β : EReal)) + (((gam * q1 : ℝ)) : EReal)) →
        ((l : EReal)) - ((eM : EReal))
            ≤ ((gam⁻¹ : ℝ) : EReal) * ((k : EReal))
              + ((gam⁻¹ : ℝ) : EReal) * ((β : EReal)) + ((q1 : EReal)) := by
      intro l eM k β q1 h
      have hkey : gam⁻¹ * ((k + β) + gam * q1) = gam⁻¹ * k + gam⁻¹ * β + q1 := by
        have hg : gam ≠ 0 := ne_of_gt hgam
        field_simp
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul] at h
      rw [hkey] at h
      rw [EReal.coe_add, EReal.coe_add, EReal.coe_mul, EReal.coe_mul] at h
      exact h
    have hbundled' : ∀ (tL l k q2 : ℝ),
        ((tL : EReal)) - ((l : EReal))
            ≤ ((lam⁻¹ : ℝ) : EReal)
              * (((k : EReal)) + (((lam * q2 : ℝ)) : EReal)) →
        ((tL : EReal)) - ((l : EReal))
            ≤ ((lam⁻¹ : ℝ) : EReal) * ((k : EReal)) + ((q2 : EReal)) := by
      intro tL l k q2 h
      have hkey : lam⁻¹ * (k + lam * q2) = lam⁻¹ * k + q2 := by
        have hl : lam ≠ 0 := ne_of_gt hlam
        field_simp
      rw [← EReal.coe_add, ← EReal.coe_mul] at h
      rw [hkey] at h
      rw [EReal.coe_add, EReal.coe_mul] at h
      exact h
    have hcombine : ∀ (tL eM l k β q1 q2 : ℝ),
        ((l : EReal)) - ((eM : EReal))
            ≤ ((gam⁻¹ : ℝ) : EReal)
              * (((k : EReal)) + ((β : EReal)) + (((gam * q1 : ℝ)) : EReal)) →
        ((tL : EReal)) - ((l : EReal))
            ≤ ((lam⁻¹ : ℝ) : EReal)
              * (((k : EReal)) + (((lam * q2 : ℝ)) : EReal)) →
        ((tL : EReal)) - ((eM : EReal))
            ≤ ((((1 : ℝ) / lam + 1 / gam) : ℝ) : EReal) * ((k : EReal))
              + ((gam⁻¹ : ℝ) : EReal) * ((β : EReal))
              + ((q1 : EReal)) + ((q2 : EReal)) := by
      intro tL eM l k β q1 q2 h1 h2
      exact hcombo tL eM l k β q1 q2 (hbundled l eM k β q1 h1) (hbundled' tL l k q2 h2)
    have hle_of_sub_le : ∀ (x y : EReal) (r : ℝ),
        x - ((r : EReal)) ≤ y → x ≤ y + ((r : EReal)) := by
      intro x y r h
      have h' : x - ((r : EReal)) + ((r : EReal)) ≤ y + ((r : EReal)) := add_le_add h le_rfl
      rwa [hsub_add_coe] at h'
    have hcancel_add_coe : ∀ (z y : EReal) (r : ℝ),
        z + ((r : EReal)) ≤ y + ((r : EReal)) → z ≤ y := by
      intro z y r h
      rcases htricho y with hy | hy | ⟨s, hs⟩
      · rw [hy] at h
        have hb : (⊥ : EReal) + ((r : EReal)) = ⊥ := by simp
        rw [hb] at h
        rcases htricho z with hz | hz | ⟨t, ht⟩
        · rw [hz, hy]
        · rw [hz] at h
          rw [htop_add r] at h
          rw [hz, hy]
          exact h
        · rw [ht] at h
          rw [← EReal.coe_add] at h
          exact absurd (le_antisymm h bot_le) (hcoe_ne_bot (t + r))
      · rw [hy]
        exact le_top
      · rw [hs, ← EReal.coe_add] at h
        rcases htricho z with hz | hz | ⟨t, ht⟩
        · rw [hz]
          exact bot_le
        · rw [hz] at h
          rw [htop_add r] at h
          exact absurd h (hnot_top_le_coe (s + r))
        · rw [ht] at h
          rw [← EReal.coe_add] at h
          rw [ht, hs]
          exact hcoe_le (by have h' := hcoe_le' h; linarith)
    have hsub_le_of_le_add : ∀ (x y : EReal) (r : ℝ),
        x ≤ y + ((r : EReal)) → x - ((r : EReal)) ≤ y := by
      intro x y r h
      exact hcancel_add_coe (x - ((r : EReal))) y r (by
        rw [hsub_add_coe]
        exact h)
    have hsub_le_of_engine : ∀ (A B R : EReal) (s : ℝ),
        B = ((s : EReal)) → A ≤ R + B → A - B ≤ R := by
      intro A B R s hB h
      rw [hB] at h ⊢
      exact hsub_le_of_le_add A R s h
    have hsub_le_general : ∀ (A B R : EReal), A ≤ R + B → A - B ≤ R := by
      intro A B R h
      rcases htricho B with hB | hB | ⟨b, hb⟩
      · rw [hB] at h ⊢
        have hb' : R + (⊥ : EReal) = ⊥ := by simp
        rw [hb'] at h
        have hA : A = ⊥ := le_antisymm h bot_le
        rw [hA]
        have hbb : (⊥ : EReal) - ⊥ = ⊥ := by simp
        rw [hbb]
        exact bot_le
      · rw [hB] at h ⊢
        have hAtop : A - (⊤ : EReal) = ⊥ := by
          rcases htricho A with h1 | h1 | ⟨a, ha⟩
          · rw [h1]; simp
          · rw [h1]; simp
          · rw [ha]; simp
        rw [hAtop]
        exact bot_le
      · rw [hb] at h ⊢
        have h' : (A - ((b : EReal))) + ((b : EReal)) ≤ R + ((b : EReal)) := by
          rw [hsub_add_coe]
          exact h
        exact hcancel_add_coe (A - ((b : EReal))) R b h'
    have hgoal_lhs : ((transferLoss M Qpost Ttask : EReal) - (empMulti M n Qpost ω : EReal))
        = (((transferLoss M Qpost Ttask - empMulti M n Qpost ω : ℝ)) : EReal) := by
      rw [EReal.coe_sub]
    have hcancel_fin : ∀ (a b l : ℝ),
        (((a : EReal)) - ((l : EReal))) + (((l : EReal)) - ((b : EReal)))
          = ((a : EReal)) - ((b : EReal)) := by
      intro a b l
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub]
      congr 1
      ring
    have hadd_ineq_coe : ∀ (a b l : ℝ) (R1 R2 : EReal),
        ((l : EReal)) - ((b : EReal)) ≤ R1 →
        ((a : EReal)) - ((l : EReal)) ≤ R2 →
        ((a : EReal)) - ((b : EReal)) ≤ R1 + R2 := by
      intro a b l R1 R2 h1 h2
      have h1' : (((l - b : ℝ)) : EReal) ≤ R1 := by
        rw [EReal.coe_sub]
        exact h1
      have h2' : (((a - l : ℝ)) : EReal) ≤ R2 := by
        rw [EReal.coe_sub]
        exact h2
      have hsum : (((a - b : ℝ)) : EReal) ≤ R1 + R2 := by
        have h := add_le_add h1' h2'
        rwa [← EReal.coe_add, show (l - b) + (a - l) = a - b by ring] at h
      rw [← EReal.coe_sub]
      exact hsum
    have hcoe_gam_inv : ((((1 : ℝ) / gam) : ℝ) : EReal) = ((gam⁻¹ : ℝ) : EReal) := by
      rw [one_div]
    have htop_add' : ∀ x : EReal, x ≠ ⊥ → (⊤ : EReal) + x = ⊤ := by
      intro x hx
      rcases htricho x with h | h | ⟨r, hr⟩
      · exact absurd h hx
      · rw [h]
        simp
      · rw [hr]
        exact htop_add r
    have hfinite_coe : ∀ x : EReal, x ≠ ⊤ → x ≠ ⊥ → ∃ r : ℝ, x = ((r : EReal)) := by
      intro x htop hbot
      rcases htricho x with h | h | h
      · exact absurd h hbot
      · exact absurd h htop
      · exact h
    have htoEReal_ne_bot : ∀ x : ENNReal, ENNReal.toEReal x ≠ ⊥ := by
      intro x
      simp
    have htop_ne_bot : (⊤ : EReal) ≠ ⊥ := by
      intro h
      exact hcoe_ne_bot 0 (le_antisymm (h ▸ le_top) bot_le)
    have hadd_ne_bot : ∀ (a b : EReal), a ≠ ⊥ → b ≠ ⊥ → a + b ≠ ⊥ := by
      intro a b ha hb
      rcases htricho a with h | h | ⟨r, hr⟩
      · exact absurd h ha
      · rw [h]
        rcases htricho b with h2 | h2 | ⟨s, hs⟩
        · exact absurd h2 hb
        · rw [h2]
          have htt : (⊤ : EReal) + ⊤ = ⊤ := by simp
          rw [htt]
          exact htop_ne_bot
        · rw [hs, htop_add s]
          exact htop_ne_bot
      · rw [hr]
        rcases htricho b with h2 | h2 | ⟨s, hs⟩
        · exact absurd h2 hb
        · rw [h2, hadd_top r]
          exact htop_ne_bot
        · rw [hs, ← EReal.coe_add]
          exact hcoe_ne_bot (r + s)
    have hsum_ne_bot : ∀ (s : Finset (Fin n)) (f : Fin n → EReal),
        (∀ i ∈ s, f i ≠ ⊥) → ∑ i ∈ s, f i ≠ ⊥ := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · intro f _
        rw [Finset.sum_empty]
        exact hcoe_ne_bot 0
      · intro a s ha ih f hf
        rw [Finset.sum_insert ha]
        exact hadd_ne_bot _ _ (hf a (Finset.mem_insert_self a s))
          (ih f fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hadd_top' : ∀ x : EReal, x ≠ ⊥ → x + (⊤ : EReal) = ⊤ := by
      intro x hx
      rcases htricho x with h | h | ⟨r, hr⟩
      · exact absurd h hx
      · rw [h]
        simp
      · rw [hr]
        exact hadd_top r
    have hadd_bot' : ∀ x : EReal, x + (⊥ : EReal) = ⊥ := by
      intro x
      rcases htricho x with h | h | ⟨r, hr⟩
      · rw [h]
        simp
      · rw [h]
        simp
      · rw [hr]
        simp
    have hbot_add' : ∀ x : EReal, (⊥ : EReal) + x = ⊥ := by
      intro x
      rcases htricho x with h | h | ⟨r, hr⟩
      · rw [h]
        simp
      · rw [h]
        simp
      · rw [hr]
        simp
    have hcoe_pos : ∀ {a : ℝ}, 0 < a → (0 : EReal) < ((a : EReal)) := by
      intro a ha
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ha)
    have hofReal_posPart : ∀ f : Θ → ℝ,
        (∫⁻ θ, ENNReal.ofReal (f θ) ∂(Qpost : Measure Θ))
          = ∫⁻ θ, ENNReal.ofReal (max (f θ) 0) ∂(Qpost : Measure Θ) := by
      intro f
      refine lintegral_congr ?_
      intro θ
      rcases le_total 0 (f θ) with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h, ENNReal.ofReal_eq_zero.mpr h, ENNReal.ofReal_zero]
    have htoEReal_ofReal_eq : ∀ {r : ℝ}, 0 ≤ r →
        ENNReal.toEReal (ENNReal.ofReal r) = ((r : EReal)) := by
      intro r hr
      simp [ENNReal.toReal_ofReal hr, hr]
    have hbridge : ∀ (f : Θ → ℝ), Integrable f (Qpost : Measure Θ) →
        ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal (f θ) ∂(Qpost : Measure Θ))
          - ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal (-(f θ)) ∂(Qpost : Measure Θ))
          = (((∫ θ, f θ ∂(Qpost : Measure Θ) : ℝ)) : EReal) := by
      intro f hf
      have hInt_abs : Integrable (fun θ : Θ => |f θ|) (Qpost : Measure Θ) := by
        simpa only [Real.norm_eq_abs] using hf.norm
      have hpos : 0 ≤ᶠ[ae (Qpost : Measure Θ)] (fun θ : Θ => |f θ|) :=
        Filter.Eventually.of_forall fun θ => abs_nonneg (f θ)
      have hlin : (∫⁻ θ, ENNReal.ofReal |f θ| ∂(Qpost : Measure Θ))
          = ENNReal.ofReal (∫ θ, |f θ| ∂(Qpost : Measure Θ)) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_abs hpos]
      have hfin1 : (∫⁻ θ, ENNReal.ofReal (f θ) ∂(Qpost : Measure Θ)) ≠ ⊤ := by
        have h1 : (∫⁻ θ, ENNReal.ofReal (f θ) ∂(Qpost : Measure Θ))
            ≤ ∫⁻ θ, ENNReal.ofReal |f θ| ∂(Qpost : Measure Θ) :=
          lintegral_mono fun θ => ENNReal.ofReal_le_ofReal (le_abs_self (f θ))
        have h2 : (∫⁻ θ, ENNReal.ofReal |f θ| ∂(Qpost : Measure Θ)) < ⊤ := by
          rw [hlin]
          exact ENNReal.ofReal_lt_top
        exact (lt_of_le_of_lt h1 h2).ne
      have hfin2 : (∫⁻ θ, ENNReal.ofReal (-(f θ)) ∂(Qpost : Measure Θ)) ≠ ⊤ := by
        have h1 : (∫⁻ θ, ENNReal.ofReal (-(f θ)) ∂(Qpost : Measure Θ))
            ≤ ∫⁻ θ, ENNReal.ofReal |f θ| ∂(Qpost : Measure Θ) :=
          lintegral_mono fun θ => by
            rw [← abs_neg (f θ)]
            exact ENNReal.ofReal_le_ofReal (le_abs_self (-(f θ)))
        have h2 : (∫⁻ θ, ENNReal.ofReal |f θ| ∂(Qpost : Measure Θ)) < ⊤ := by
          rw [hlin]
          exact ENNReal.ofReal_lt_top
        exact (lt_of_le_of_lt h1 h2).ne
      have e1 : ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal (f θ) ∂(Qpost : Measure Θ))
          = (((∫⁻ θ, ENNReal.ofReal (f θ) ∂(Qpost : Measure Θ)).toReal : ℝ) : EReal) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfin1]
        exact htoEReal_ofReal_eq ENNReal.toReal_nonneg
      have e2 : ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal (-(f θ)) ∂(Qpost : Measure Θ))
          = (((∫⁻ θ, ENNReal.ofReal (-(f θ)) ∂(Qpost : Measure Θ)).toReal : ℝ) : EReal) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfin2]
        exact htoEReal_ofReal_eq ENNReal.toReal_nonneg
      rw [e1, e2, ← EReal.coe_sub,
        ← MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    have hT_bridge : ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal
          (∫ p, transferAt M θ p ∂(Ttask : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
          ∂(Qpost : Measure Θ))
        - ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal
          (-(∫ p, transferAt M θ p ∂(Ttask : Measure (ProbabilityMeasure (X × Y) × ℕ+))))
          ∂(Qpost : Measure Θ))
        = (transferLoss M Qpost Ttask : EReal) :=
      hbridge (fun θ => ∫ p, transferAt M θ p ∂(Ttask : Measure (ProbabilityMeasure (X × Y) × ℕ+)))
        (hTransferLoss_int Qpost)
    have hE_bridge : ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i : Fin n,
          LgibbsEmp M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (SOF ω i))
          ∂(Qpost : Measure Θ))
        - ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal (-((1 / (n : ℝ)) * ∑ i : Fin n,
          LgibbsEmp M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (SOF ω i)))
          ∂(Qpost : Measure Θ))
        = (empMulti M n Qpost ω : EReal) :=
      hbridge (fun θ => (1 / (n : ℝ)) * ∑ i : Fin n,
          LgibbsEmp M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (SOF ω i))
        (hEmpMulti_int Qpost ω)
    have hbase_data := statopia_math_node_512556819_d2fb8272 M hloss hloss_int hLgibbs_int
      hLgibbsEmp_int HP gam hgam n hn ω (hPi1Exp_int ω) (hPi1Inner_int ω) hmeas_prior
    have hφ_meas : Measurable φ := hbase_data.1
    have hExp_mu : Integrable (fun x : Θ × (Fin n → U) => Real.exp (gam * φ x)) μ :=
      hbase_data.2.1
    have hlog_int : (∫ x : Θ × (Fin n → U), Real.exp (gam * φ x) ∂μ)
        = ∫ θ : Θ, Pi1Inner M n gam ω θ ∂(HP : Measure Θ) := hbase_data.2.2
    have hprob_pi : ∀ θ : Θ, IsProbabilityMeasure
        (Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) :=
      fun θ => inferInstance
    have hprob_pi_P : ∀ θ : Θ, IsProbabilityMeasure
        (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) :=
      fun θ => inferInstance
    have hmap_mass : ∀ θ : Θ,
        ((Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) Set.univ = 1 := by
      intro θ
      have h1 : (Measure.map (fun u : Fin n → U => (θ, u))
            (Measure.pi fun i : Fin n =>
              (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) Set.univ
          = (Measure.pi fun i : Fin n =>
              (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) Set.univ :=
        MeasureTheory.Measure.map_apply (measurable_const.prodMk measurable_id)
          MeasurableSet.univ
      rw [h1]
      exact (hprob_pi θ).measure_univ
    have hmap_mass_P : ∀ θ : Θ,
        ((Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) Set.univ = 1 := by
      intro θ
      have h1 : (Measure.map (fun u : Fin n → U => (θ, u))
            (Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U))) Set.univ
          = (Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) Set.univ :=
        MeasureTheory.Measure.map_apply (measurable_const.prodMk measurable_id)
          MeasurableSet.univ
      rw [h1]
      exact (hprob_pi_P θ).measure_univ
    have hmap_prob : ∀ θ : Θ, IsProbabilityMeasure
        ((Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) :=
      fun θ => ⟨hmap_mass θ⟩
    have hmap_prob_P : ∀ θ : Θ, IsProbabilityMeasure
        ((Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) :=
      fun θ => ⟨hmap_mass_P θ⟩
    have hlint_one : (∫⁻ θ, (1 : ENNReal) ∂(Qpost : Measure Θ)) = 1 := by
      simp
    have hker_mass : (∫⁻ θ, ((Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) Set.univ ∂(Qpost : Measure Θ)) = 1 := by
      rw [lintegral_congr (fun θ => hmap_mass θ)]
      exact hlint_one


    have hker_mass_P : (∫⁻ θ, ((Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) Set.univ ∂(HP : Measure Θ)) = 1 := by
      rw [lintegral_congr (fun θ => hmap_mass_P θ)]
      simp
    have hpi_sigma : (inferInstance : MeasurableSpace (Fin n → U))
        = ⨆ i : Fin n, MeasurableSpace.comap (fun u : Fin n → U => u i)
            (inferInstance : MeasurableSpace U) := rfl
    have hprod_sigma : (inferInstance : MeasurableSpace (Θ × (Fin n → U)))
        = MeasurableSpace.comap (fun p : Θ × (Fin n → U) => p.1)
            (inferInstance : MeasurableSpace Θ)
          ⊔ MeasurableSpace.comap (fun p : Θ × (Fin n → U) => p.2)
              (inferInstance : MeasurableSpace (Fin n → U)) := rfl
    have hpi_box : ∀ (θ : Θ) (B : Fin n → Set U), (∀ i, MeasurableSet (B i)) →
        (Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) (Set.univ.pi B)
          = ∏ i, (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (B i) := by
      intro θ B hB
      simp
    have hbox_meas : ∀ (B : Fin n → Set U), (∀ i, MeasurableSet (B i)) →
        MeasurableSet (Set.univ.pi B) := by
      intro B hB
      have hEq : Set.univ.pi B = ⋂ i : Fin n, (fun u : Fin n → U => u i) ⁻¹' (B i) := by
        ext u
        simp
      rw [hEq]
      exact MeasurableSet.iInter fun i => measurable_pi_apply i (hB i)
    have hgen_pi_le : MeasurableSpace.generateFrom {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
        (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B}
        ≤ (inferInstance : MeasurableSpace (Fin n → U)) := by
      refine MeasurableSpace.generateFrom_le ?_
      intro s hs
      obtain ⟨B, hB, rfl⟩ := hs
      exact hbox_meas B hB
    have hbox_eq : ∀ (i : Fin n) (B : Set U),
        (fun u : Fin n → U => u i) ⁻¹' B
          = Set.univ.pi (fun j => if j = i then B else Set.univ) := by
      intro i B
      ext u
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · rintro h j
        by_cases hj : j = i
        · rw [← hj] at h
          rwa [if_pos hj]
        · simpa only [if_neg hj] using Set.mem_univ (u j)
      · rintro h
        simpa only [if_pos rfl] using h i
    have hgen_pi_ge : (inferInstance : MeasurableSpace (Fin n → U))
        ≤ MeasurableSpace.generateFrom {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
            (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B} := by
      rw [hpi_sigma]
      refine iSup_le fun i => ?_
      intro t ht
      obtain ⟨B, hB, hBt⟩ := ht
      rw [← hBt]
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨fun j => if j = i then B else Set.univ, fun j => by
          by_cases h : j = i
          · simpa only [if_pos h] using hB
          · simpa only [if_neg h] using MeasurableSet.univ, hbox_eq i B⟩
    have hgen_pi : (inferInstance : MeasurableSpace (Fin n → U))
        = MeasurableSpace.generateFrom {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
            (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B} :=
      le_antisymm hgen_pi_ge hgen_pi_le
    have hispi_box : IsPiSystem {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
        (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B} := by
      intro s hs t ht _
      obtain ⟨B, hB, rfl⟩ := hs
      obtain ⟨B', hB', rfl⟩ := ht
      exact ⟨fun i => B i ∩ B' i, fun i => (hB i).inter (hB' i), by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies]
        exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩⟩
    have hpi_eval : ∀ s ∈ {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
        (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B},
        Measurable fun θ : Θ => (Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) s := by
      rintro s ⟨B, hB, rfl⟩
      have hfac : ∀ i : Fin n, Measurable fun θ : Θ =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (B i) :=
        fun i => (MeasureTheory.Measure.measurable_measure.mp (hmeas_post i)) (B i) (hB i)
      have hrew : (fun θ : Θ => (Measure.pi fun i : Fin n =>
            (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) (Set.univ.pi B))
          = fun θ => ∏ i : Fin n,
              (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (B i) := by
        funext θ
        exact hpi_box θ B hB
      rw [hrew]
      exact Finset.measurable_prod Finset.univ fun i _ => hfac i
    have hpi_meas : Measurable fun θ : Θ => Measure.pi fun i : Fin n =>
        (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) := by
      haveI : ∀ θ : Θ, IsProbabilityMeasure (Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) := hprob_pi
      exact Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
        (S := {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
          (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B}) hgen_pi hispi_box hpi_eval


    have hker_ae :
        AEMeasurable (fun θ : Θ => (Measure.pi fun i : Fin n =>
            (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) (Qpost : Measure Θ) ∧
        AEMeasurable (fun θ : Θ => (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u : Fin n → U => (θ, u))) (HP : Measure Θ) := by
      have hpi_eval_P : ∀ s ∈ {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
          (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B},
          Measurable fun θ : Θ => (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) s := by
        rintro s ⟨B, hB, rfl⟩
        have hfac : ∀ i : Fin n, Measurable fun θ : Θ =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (B i) :=
          fun i => (MeasureTheory.Measure.measurable_measure.mp (hmeas_prior i)) (B i) (hB i)
        have hrew : (fun θ : Θ => (Measure.pi fun i : Fin n =>
              (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) (Set.univ.pi B))
            = fun θ => ∏ i : Fin n,
                (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (B i) := by
          funext θ
          simp
        rw [hrew]
        exact Finset.measurable_prod Finset.univ fun i _ => hfac i
      have hpi_meas_P : Measurable fun θ : Θ => Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) := by
        haveI : ∀ θ : Θ, IsProbabilityMeasure (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)) := hprob_pi_P
        exact Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
          (S := {s : Set (Fin n → U) | ∃ B : Fin n → Set U,
            (∀ i, MeasurableSet (B i)) ∧ s = Set.univ.pi B}) hgen_pi hispi_box hpi_eval_P
      have hker_post_meas : Measurable fun θ : Θ => (Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
          (fun u : Fin n → U => (θ, u)) := by
        let κ : ProbabilityTheory.Kernel Θ (Fin n → U) :=
          ⟨fun θ => Measure.pi fun i : Fin n =>
            (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U), hpi_meas⟩
        have hκ : ∀ a : Θ, (κ a) = Measure.pi fun i : Fin n =>
            (basePost M ((mOf ω i : ℕ)) (SOF ω i) a : Measure U) := fun a => rfl
        have hfin : ∀ a : Θ, IsFiniteMeasure (κ a) := by
          intro a
          have h1 : (κ a) Set.univ = 1 := by
            rw [hκ a]
            exact (hprob_pi a).measure_univ
          exact ⟨by rw [h1]; exact ENNReal.one_lt_top⟩
        refine MeasureTheory.Measure.measurable_measure.mpr (fun t ht => ?_)
        show Measurable fun b : Θ => (Measure.map (fun u : Fin n → U => (b, u))
          (Measure.pi fun i : Fin n =>
            (basePost M ((mOf ω i : ℕ)) (SOF ω i) b : Measure U))) t
        have hfun : (fun b : Θ => (Measure.map (fun u : Fin n → U => (b, u))
              (Measure.pi fun i : Fin n =>
                (basePost M ((mOf ω i : ℕ)) (SOF ω i) b : Measure U))) t)
            = fun b : Θ => (κ b) (Prod.mk b ⁻¹' t) := by
          funext b
          exact MeasureTheory.Measure.map_apply (measurable_const.prodMk measurable_id) ht
        rw [hfun]
        exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite ht hfin
      have hker_prior_meas : Measurable fun θ : Θ => (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
          (fun u : Fin n → U => (θ, u)) := by
        let κ : ProbabilityTheory.Kernel Θ (Fin n → U) :=
          ⟨fun θ => Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U), hpi_meas_P⟩
        have hκ : ∀ a : Θ, (κ a) = Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) a : Measure U) := fun a => rfl
        have hfin : ∀ a : Θ, IsFiniteMeasure (κ a) := by
          intro a
          have h1 : (κ a) Set.univ = 1 := by
            rw [hκ a]
            exact (hprob_pi_P a).measure_univ
          exact ⟨by rw [h1]; exact ENNReal.one_lt_top⟩

        refine MeasureTheory.Measure.measurable_measure.mpr (fun t ht => ?_)
        show Measurable fun b : Θ => (Measure.map (fun u : Fin n → U => (b, u))
          (Measure.pi fun i : Fin n =>
            (basePrior M ((mOf ω i : ℕ)) (SOF ω i) b : Measure U))) t
        have hfun : (fun b : Θ => (Measure.map (fun u : Fin n → U => (b, u))
              (Measure.pi fun i : Fin n =>
                (basePrior M ((mOf ω i : ℕ)) (SOF ω i) b : Measure U))) t)
            = fun b : Θ => (κ b) (Prod.mk b ⁻¹' t) := by
          funext b
          exact MeasureTheory.Measure.map_apply (measurable_const.prodMk measurable_id) ht
        rw [hfun]
        exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite ht hfin
      exact ⟨hker_post_meas.aemeasurable, hker_prior_meas.aemeasurable⟩
    have hν_mass : ν Set.univ = 1 := by
      have h := hker_ae.1
      rw [show ν = (Qpost : Measure Θ).bind (fun θ => (Measure.pi fun i : Fin n =>
          (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u => (θ, u))) from rfl,
        MeasureTheory.Measure.bind_apply MeasurableSet.univ h]
      exact hker_mass
    have hμ_mass : μ Set.univ = 1 := by
      have h := hker_ae.2
      rw [show μ = (HP : Measure Θ).bind (fun θ => (Measure.pi fun i : Fin n =>
          (basePrior M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U)).map
            (fun u => (θ, u))) from rfl,
        MeasureTheory.Measure.bind_apply MeasurableSet.univ h]
      exact hker_mass_P
    let νP : ProbabilityMeasure (Θ × (Fin n → U)) := ⟨ν, ⟨hν_mass⟩⟩
    let μP : ProbabilityMeasure (Θ × (Fin n → U)) := ⟨μ, ⟨hμ_mass⟩⟩
    have hbase_engine :
        ENNReal.toEReal
            (∫⁻ x, ENNReal.ofReal (φ x) ∂(νP : Measure (Θ × (Fin n → U))))
          ≤ ((gam⁻¹ : ℝ) : EReal)
              * (ENNReal.toEReal
                    (InformationTheory.klDiv (νP : Measure (Θ × (Fin n → U)))
                      (μP : Measure (Θ × (Fin n → U))))
                + ((Real.log
                    (∫ x : Θ × (Fin n → U),
                      Real.exp (gam * φ x) ∂(μP : Measure (Θ × (Fin n → U)))) : ℝ) : EReal))
            + ENNReal.toEReal
                (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂(νP : Measure (Θ × (Fin n → U)))) :=
      statopia_math_node_4000542074_30367f47 μP νP gam hgam φ hφ_meas hExp_mu
    rw [show (∫ x : Θ × (Fin n → U), Real.exp (gam * φ x)
          ∂(μP : Measure (Θ × (Fin n → U))))
        = ∫ θ : Θ, Pi1Inner M n gam ω θ ∂(HP : Measure Θ) from hlog_int] at hbase_engine
    have hKL_base : ENNReal.toEReal
          (InformationTheory.klDiv (νP : Measure (Θ × (Fin n → U)))
            (μP : Measure (Θ × (Fin n → U))))
        = ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
          + baseKLSum M n Qpost ω := hKLchain'
    have hbase_engine' :
        ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (φ x) ∂ν)
          ≤ ((gam⁻¹ : ℝ) : EReal)
              * ((ENNReal.toEReal
                    (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
                  + baseKLSum M n Qpost ω)
                + ((gam * Pi1 M n HP gam ω : ℝ) : EReal))
            + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂ν) := by
      have h := hbase_engine
      rw [hKL_base, hlog_pi1] at h
      exact h
    have hmeta_ac' : (Qpost : Measure Θ) ≪ (HP : Measure Θ) →
        ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (ψ x) ∂(Qpost : Measure Θ))
          ≤ ((lam⁻¹ : ℝ) : EReal)
              * (ENNReal.toEReal
                  (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
                + ((lam * Pi2 M n Ttask HP lam ω : ℝ) : EReal))
            + ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(ψ x)) ∂(Qpost : Measure Θ)) := by
      intro hac
      have h := hmeta_ac hac
      rw [hlog_pi2] at h
      exact h
    let G : Θ → ℝ := fun θ => (1 / (n : ℝ)) * ∑ i : Fin n,
      Lgibbs M.ℓ (basePost M ((mOf ω i : ℕ)) (SOF ω i) θ : Measure U) (DOf ω i : Measure (X × Y))
    let Lt : EReal := ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal (G θ) ∂(Qpost : Measure Θ))
      - ENNReal.toEReal (∫⁻ θ, ENNReal.ofReal (-(G θ)) ∂(Qpost : Measure Θ))
    have hbridge_prod : ∀ (f : Θ × (Fin n → U) → ℝ), Integrable f ν →
        ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (f x) ∂ν)
          - ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(f x)) ∂ν)
          = (((∫ x, f x ∂ν : ℝ)) : EReal) := by
      intro f hf
      have hInt_abs : Integrable (fun x : Θ × (Fin n → U) => |f x|) ν := by
        simpa only [Real.norm_eq_abs] using hf.norm
      have hpos : 0 ≤ᶠ[ae ν] (fun x : Θ × (Fin n → U) => |f x|) :=
        Filter.Eventually.of_forall fun x => abs_nonneg (f x)
      have hlin : (∫⁻ x, ENNReal.ofReal |f x| ∂ν) = ENNReal.ofReal (∫ x, |f x| ∂ν) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_abs hpos]
      have hfin1 : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≠ ⊤ := by
        have h1 : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂ν :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (le_abs_self (f x))
        have h2 : (∫⁻ x, ENNReal.ofReal |f x| ∂ν) < ⊤ := by
          rw [hlin]
          exact ENNReal.ofReal_lt_top
        exact (lt_of_le_of_lt h1 h2).ne
      have hfin2 : (∫⁻ x, ENNReal.ofReal (-(f x)) ∂ν) ≠ ⊤ := by
        have h1 : (∫⁻ x, ENNReal.ofReal (-(f x)) ∂ν) ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂ν :=
          lintegral_mono fun x => by
            rw [← abs_neg (f x)]
            exact ENNReal.ofReal_le_ofReal (le_abs_self (-(f x)))
        have h2 : (∫⁻ x, ENNReal.ofReal |f x| ∂ν) < ⊤ := by
          rw [hlin]
          exact ENNReal.ofReal_lt_top
        exact (lt_of_le_of_lt h1 h2).ne
      have e1 : ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (f x) ∂ν)
          = (((∫⁻ x, ENNReal.ofReal (f x) ∂ν).toReal : ℝ) : EReal) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfin1]
        exact htoEReal_ofReal_eq ENNReal.toReal_nonneg
      have e2 : ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(f x)) ∂ν)
          = (((∫⁻ x, ENNReal.ofReal (-(f x)) ∂ν).toReal : ℝ) : EReal) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfin2]
        exact htoEReal_ofReal_eq ENNReal.toReal_nonneg
      rw [e1, e2, ← EReal.coe_sub,
        ← MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    by_cases htop : ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)) = ⊤
        ∨ baseKLSum M n Qpost ω = ⊤
    · have hmul_top : ∀ {c : ℝ}, 0 < c → ((c : EReal) * (⊤ : EReal)) = ⊤ := by
        intro c hc
        rw [show ((c : EReal) * (⊤ : EReal))
          = (if 0 < c then (⊤ : EReal) else if c = 0 then (0 : EReal) else ⊥) from rfl,
          if_pos hc]
      have h1 : (0 : ℝ) < 1 / lam := by positivity
      have h2 : (0 : ℝ) < 1 / gam := by positivity
      have hcpos : (0 : ℝ) < (1 : ℝ) / lam + 1 / gam := by linarith
      have hC1 : (((1 : ℝ) / lam + 1 / gam) : EReal)
          = ((((1 : ℝ) / lam + 1 / gam : ℝ)) : EReal) := rfl
      have hC2 : (((1 : ℝ) / gam) : EReal) = ((((1 : ℝ) / gam : ℝ)) : EReal) := rfl
      have hβne : baseKLSum M n Qpost ω ≠ ⊥ := by
        simp only [baseKLSum]
        exact hsum_ne_bot Finset.univ _ (fun i _ => htoEReal_ne_bot _)
      have htt : (⊤ : EReal) + ⊤ = ⊤ := by simp
      by_cases hK : ENNReal.toEReal
          (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)) = ⊤
      · rcases htricho (baseKLSum M n Qpost ω) with hb | hb | ⟨b, hbb⟩
        · exact absurd hb hβne
        · rw [hK, hC1, hmul_top (c := (1 : ℝ) / lam + 1 / gam) hcpos, hb, hC2,
            hmul_top (c := (1 : ℝ) / gam) h2]
          rw [htt, htop_add (Pi1 M n HP gam ω), htop_add (Pi2 M n Ttask HP lam ω)]
          exact le_top
        · rw [hK, hC1, hmul_top (c := (1 : ℝ) / lam + 1 / gam) hcpos, hbb, hC2,
            ← EReal.coe_mul]
          rw [htop_add (((1 : ℝ) / gam) * b), htop_add (Pi1 M n HP gam ω),
            htop_add (Pi2 M n Ttask HP lam ω)]
          exact le_top
      · have hβtop : baseKLSum M n Qpost ω = ⊤ := by
          rcases htop with h | h
          · exact absurd h hK
          · exact h
        obtain ⟨k, hk⟩ := hfinite_coe
          (ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)))
          hK (htoEReal_ne_bot _)
        rw [hk, hC1, ← EReal.coe_mul, hβtop, hC2,
          hmul_top (c := (1 : ℝ) / gam) h2,
          hadd_top (((1 : ℝ) / lam + 1 / gam) * k)]
        rw [htop_add (Pi1 M n HP gam ω), htop_add (Pi2 M n Ttask HP lam ω)]
        exact le_top
    · push_neg at htop
      obtain ⟨hKtop, hβtop⟩ := htop
      have hβne : baseKLSum M n Qpost ω ≠ ⊥ := by
        simp only [baseKLSum]
        exact hsum_ne_bot Finset.univ _ (fun i _ => htoEReal_ne_bot _)
      obtain ⟨k, hk⟩ := hfinite_coe
        (ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ)))
        hKtop (htoEReal_ne_bot _)
      obtain ⟨βr, hβr⟩ := hfinite_coe (baseKLSum M n Qpost ω) hβtop hβne
      have hchild := statopia_math_node_2469337524_a68c5ec1 M hloss HP lam gam hlam hgam n hn
        Ttask ω Qpost hPrior_meas hPost_meas hKL_meas hloss_int hLgibbs_int hLgibbsEmp_int
        hTransferLoss_int hEmpMulti_int hPi1Exp_int hPi1Inner_int hPi2Exp_int hKtop hβtop
      obtain ⟨hGint0, hφint0, hident0, hAC⟩ := hchild
      have hGint : Integrable G (Qpost : Measure Θ) := hGint0
      have hφint : Integrable φ ν := hφint0
      have hident : (∫ x, φ x ∂ν)
          = (∫ θ, G θ ∂(Qpost : Measure Θ)) - empMulti M n Qpost ω := hident0
      have hGbridge : Lt = (((∫ θ, G θ ∂(Qpost : Measure Θ) : ℝ)) : EReal) :=
        hbridge G hGint
      have hLG : Lt - (empMulti M n Qpost ω : EReal)
          = (((∫ θ, G θ ∂(Qpost : Measure Θ) - empMulti M n Qpost ω : ℝ)) : EReal) := by
        rw [hGbridge, ← EReal.coe_sub]
      have hφid : (((∫ θ, G θ ∂(Qpost : Measure Θ) - empMulti M n Qpost ω : ℝ)) : EReal)
          = ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (φ x) ∂ν)
            - ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(φ x)) ∂ν) := by
        rw [← hident]
        exact (hbridge_prod φ hφint).symm
      have h52 : Lt - (empMulti M n Qpost ω : EReal)
          ≤ ((gam⁻¹ : ℝ) : EReal)
            * ((ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
                + baseKLSum M n Qpost ω) + ((gam * Pi1 M n HP gam ω : ℝ) : EReal)) := by
        rw [hLG, hφid]
        exact hsub_le_general _ _ _ hbase_engine'
      have hψint : Integrable ψ (Qpost : Measure Θ) :=
        (hTransferLoss_int Qpost).sub hGint
      have hψbridge : ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (ψ x) ∂(Qpost : Measure Θ))
          - ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(ψ x)) ∂(Qpost : Measure Θ))
          = (((∫ x, ψ x ∂(Qpost : Measure Θ) : ℝ)) : EReal) := hbridge ψ hψint
      have hψ_int_eq : (∫ x, ψ x ∂(Qpost : Measure Θ))
          = transferLoss M Qpost Ttask - ∫ θ, G θ ∂(Qpost : Measure Θ) := by
        simp only [ψ, transferLoss, G]
        exact integral_sub (hTransferLoss_int Qpost) hGint
      have h54 : (transferLoss M Qpost Ttask : EReal) - Lt
          ≤ ((lam⁻¹ : ℝ) : EReal)
            * (ENNReal.toEReal (InformationTheory.klDiv (Qpost : Measure Θ) (HP : Measure Θ))
                + ((lam * Pi2 M n Ttask HP lam ω : ℝ) : EReal)) := by
        have hTL : (transferLoss M Qpost Ttask : EReal) - Lt
            = ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (ψ x) ∂(Qpost : Measure Θ))
              - ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (-(ψ x)) ∂(Qpost : Measure Θ)) := by
          rw [hGbridge, ← EReal.coe_sub, hψbridge, hψ_int_eq]
        rw [hTL]
        exact hsub_le_general _ _ _ (hmeta_ac' hAC)

      have hLttop : Lt ≠ ⊤ := by
        intro hLt
        have h := h52
        rw [hLt, hk, hβr, hsub_top] at h
        rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul] at h
        exact hnot_top_le_coe _ h
      have hLtbot : Lt ≠ ⊥ := by
        intro hLt
        have h := h54
        rw [hLt, hk, hsub_bot] at h
        rw [← EReal.coe_add, ← EReal.coe_mul] at h
        exact hnot_top_le_coe _ h
      obtain ⟨l, hl⟩ := hfinite_coe Lt hLttop hLtbot
      have h1 := h52
      rw [hl, hk, hβr] at h1
      have h2 := h54
      rw [hl, hk] at h2
      rw [hk, hβr]
      have hc := hcombine (transferLoss M Qpost Ttask) (empMulti M n Qpost ω) l k βr
        (Pi1 M n HP gam ω) (Pi2 M n Ttask HP lam ω) h1 h2
      rwa [← hcoe_gam_inv] at hc
  have hstep := add_le_add_right hcore ((empMulti M n Qpost ω : EReal))
  have hcancel : (empMulti M n Qpost ω : EReal)
      + ((transferLoss M Qpost Ttask : EReal) - (empMulti M n Qpost ω : EReal))
      = (transferLoss M Qpost Ttask : EReal) := by
    rw [add_comm, ← EReal.coe_sub, ← EReal.coe_add, sub_add_cancel]
  rw [hcancel] at hstep
  refine hstep.trans (le_of_eq ?_)
  ac_rfl
  /- @proof-region region.target-node.session.c5d174388277d0fc end -/

end
end Statlib.Imported
