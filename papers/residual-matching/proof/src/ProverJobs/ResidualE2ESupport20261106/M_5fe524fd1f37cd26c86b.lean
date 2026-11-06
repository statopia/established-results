import Statlib.HighDim.MatrixAnalysis.SingularValueProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_f00de8b445341c78f04b
import ProverJobs.ResidualE2ESupport20261106.M_9f6712965bbb2a8f758c
import ProverJobs.ResidualE2ESupport20261106.M_a672c9317c853e441ad0
import ProverJobs.ResidualE2ESupport20261106.M_7fa59ac9d397d8763423
import ProverJobs.ResidualE2ESupport20261106.M_3d77f1105c4f1bdef034

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ResidualLoss20261106.Statlib.Imported
universe u
set_option maxHeartbeats 300000
noncomputable section

/-- The finite deterministic calibration step used after the noise and Monte-Carlo
spectra have both been localized around the same MP quantiles. -/
theorem spectral_calibration_on_good_spectra
    (rhoMin : ℝ) (hrhoMin : 0 < rhoMin)
    (m n : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m)
    (p sigma : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hsigma : 0 < sigma)
    (Om M0 Hm : Matrix (Fin m) (Fin n) ℝ)
    (hOm : ∀ i j, Om i j = 0 ∨ Om i j = 1)
    (gam lamHat w : Fin n → ℝ)
    (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hgamLower : ∀ i ∈ indexSet n, Real.pi * rhoMin / 12 ≤ gam i)
    (hgamUpper : ∀ i, gam i ≤ 2)
    (CI CL : ℝ) (hCI : 0 < CI) (hCL : 0 < CL)
    (hCI_small : CI * deltaM m ≤ 1)
    (hCL_small : CL * deltaM m ≤ Real.pi * rhoMin / 12 / 2)
    (hcal_small : ((CI + CL) / (Real.pi * rhoMin / 12 / 22)) * deltaM m ≤ 1/2)
    (hnoise : ∀ i, |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) - Real.sqrt p * gam i|
      ≤ CI * Real.sqrt p * deltaM m)
    (hlam : ∀ i, |lamHat i - Real.sqrt p * gam i| ≤ CL * Real.sqrt p * deltaM m) :
    let cb := Real.pi * rhoMin / 12 / 22
    let C1 := CI + CL
    let C4 := C1 / cb
    (∀ i, |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) - lamHat i|
      ≤ C1 * Real.sqrt p * deltaM m) ∧
    (cb * (n:ℝ) * Real.sqrt p ≤ ∑ i ∈ indexSet n, lamHat i) ∧
    (|sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M0 / sigma - 1|
      ≤ C4 * deltaM m) ∧
    (loss hnm (indexSet n) p w lamHat (Yobs Om M0 Hm) Om M0
      ≤ ENNReal.ofReal ((2 * C1^2 + 8 * C4^2 * 3^2) * deltaM m^2)) ∧
    (∀ M : Matrix (Fin m) (Fin n) ℝ,
      |sigmaHat hnm (indexSet n) lamHat (Yobs Om M0 Hm) Om M / sigma - 1|
      ≤ C4 * deltaM m + (1/cb) * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp Om (M-M0))
        / (sigma * Real.sqrt ((m:ℝ)*(n:ℝ)*p))) := by
  dsimp only
  have hn1 : 1 ≤ n := by omega
  have hm2 : 2 ≤ m := hn.trans hnm
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hdelta : 0 ≤ deltaM m := by
    unfold deltaM
    exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m)))
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hcb : 0 < Real.pi * rhoMin / 12 / 22 := by positivity
  have hC1 : 0 < CI + CL := add_pos hCI hCL
  have hC4 : 0 < (CI+CL) / (Real.pi * rhoMin / 12 / 22) := div_pos hC1 hcb
  have hclose : ∀ i, |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) - lamHat i|
      ≤ (CI+CL) * Real.sqrt p * deltaM m := by
    intro i
    calc
      |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) - lamHat i|
        ≤ |sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) - Real.sqrt p * gam i| +
          |lamHat i - Real.sqrt p * gam i| := by
          simpa only [abs_sub_comm (Real.sqrt p * gam i) (lamHat i)] using
            abs_sub_le (sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ))) (Real.sqrt p * gam i) (lamHat i)
      _ ≤ CI * Real.sqrt p * deltaM m + CL * Real.sqrt p * deltaM m := add_le_add (hnoise i) (hlam i)
      _ = (CI+CL) * Real.sqrt p * deltaM m := by ring
  have hden := (statopia_math_node_2486598710_e2ce0d5f rhoMin hrhoMin m n hn hnm p hp0 hp1
    gam lamHat hgamLower CL hCL hlam hCL_small).1
  have hcal := statopia_math_node_3877234010_7a806c4e m n hn1 hnm p sigma hp0 hp1 hsigma
    Om M0 Hm hOm lamHat (CI+CL) (Real.pi * rhoMin / 12 / 22) hC1 hcb hclose hden
  have h3 : ∀ i, 0 ≤ sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) ∧
      sv hnm (maskOp Om Hm) i / (sigma * Real.sqrt (m:ℝ)) ≤ 3 * Real.sqrt p := by
    intro i
    constructor
    · apply div_nonneg _ (mul_nonneg hsigma.le (Real.sqrt_nonneg _))
      unfold sv Statlib.HighDim.MatrixAnalysis.singularValues
      exact Real.sqrt_nonneg _
    · have hu := (abs_le.mp (hnoise i)).2
      have hg := mul_le_mul_of_nonneg_left (hgamUpper i) hsp
      have hc := mul_le_mul_of_nonneg_right hCI_small hsp
      nlinarith
  have hloss := (statopia_math_node_2587526204_66177347 m n p sigma hn1 hnm hp0 hp1 hsigma
    Om M0 Hm hOm lamHat w hw_nn hw_sum (CI+CL) 3 ((CI+CL)/(Real.pi*rhoMin/12/22))
    hC1 (by norm_num) hC4 hclose h3 hcal.2.1 hcal_small).2
  exact ⟨hclose, hden, hcal.2.1, hloss, hcal.1⟩

/-- The full entry independence in the sampling law implies the actual independence
of the random mask and the entire Monte-Carlo block. -/
theorem sampling_law_components {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n T : ℕ}
    (Om Hm : Ω → Matrix (Fin m) (Fin n) ℝ)
    (G : Ω → Fin T → Matrix (Fin m) (Fin n) ℝ) (p sigma K : ℝ)
    (hlaw : IsSamplingLaw μ Om Hm G p sigma K) :
    IsBernoulliMask μ Om p ∧ IsGaussianDrawsLaw μ G ∧ IndepFun Om G μ ∧
    iIndepFun (fun k : (Fin m × Fin n) ⊕ (Fin m × Fin n) => fun s =>
      match k with | Sum.inl q => Om s q.1 q.2 | Sum.inr q => Hm s q.1 q.2) μ := by
  classical
  rcases hlaw with ⟨hOm, hbin, hprob, hHm, hint, hmean, hint2, hvar, htail, hG, hGlaw, hi⟩
  have hmask : IsBernoulliMask μ Om p := ⟨hOm, hbin, hprob, hi.precomp Sum.inl_injective⟩
  have hdraws : IsGaussianDrawsLaw μ G := ⟨hG, hGlaw,
    hi.precomp (Sum.inr_injective.comp Sum.inr_injective)⟩
  refine ⟨hmask, hdraws, ?_, ?_⟩
  · let S : Finset (lawIndex m n T) := Finset.univ.image Sum.inl
    let Q : Finset (lawIndex m n T) := Finset.univ.image (fun q => Sum.inr (Sum.inr q))
    have hd : Disjoint S Q := by
      simp only [S, Q, Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
      rintro k ⟨i, rfl⟩ ⟨j, hj⟩
      cases hj
    have hm : ∀ k : lawIndex m n T, Measurable (fun s => lawVar (Om s) (Hm s) (G s) k) := by
      intro k
      rcases k with q | (q | q)
      · exact hOm q.1 q.2
      · exact hHm q.1 q.2
      · exact hG q.1 q.2.1 q.2.2
    have hblock := hi.indepFun_finset S Q hd hm
    let es : Fin m × Fin n → S := fun q => ⟨Sum.inl q, by simp [S]⟩
    let eq : Fin T × Fin m × Fin n → Q := fun q => ⟨Sum.inr (Sum.inr q), by simp [Q]⟩
    have hs : Measurable (fun z : S → ℝ => fun i : Fin m => fun j : Fin n => z (es (i,j))) :=
      measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => measurable_pi_apply _))
    have hq : Measurable (fun z : Q → ℝ => fun t : Fin T => fun i : Fin m => fun j : Fin n => z (eq (t,i,j))) :=
      measurable_pi_iff.2 (fun t => measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => measurable_pi_apply _)))
    exact hblock.comp hs hq
  · let e : ((Fin m × Fin n) ⊕ (Fin m × Fin n)) → lawIndex m n T :=
      Sum.elim Sum.inl (fun q => Sum.inr (Sum.inl q))
    have he : Function.Injective e := by
      intro a b h
      cases a <;> cases b <;> simp [e] at h ⊢ <;> exact h
    convert hi.precomp he using 1
    funext k s
    cases k <;> rfl

lemma measurable_masked_singular_pair {m n : ℕ} (hnm : n ≤ m) (i : Fin n) :
    Measurable (fun x : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      sv hnm (maskOp x.1 ((Real.sqrt (m:ℝ))⁻¹ • x.2)) i) := by
  have hm : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      maskOp x.1 ((Real.sqrt (m:ℝ))⁻¹ • x.2)) := by
    refine measurable_pi_iff.2 (fun a => measurable_pi_iff.2 (fun b => ?_))
    change Measurable (fun x : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      x.1 a b * ((Real.sqrt (m:ℝ))⁻¹ * x.2 a b))
    fun_prop
  unfold sv
  exact (statopia_math_node_3334131066_c2302711 (Fin.castLE (le_min hnm le_rfl) i)).comp hm


lemma measurable_lambdaCirc {m n : ℕ} (hnm : n ≤ m)
    (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure μG] (i : Fin n) :
    Measurable (fun O : Matrix (Fin m) (Fin n) ℝ => lambdaCirc hnm μG O i) := by
  unfold lambdaCirc
  have hh := StronglyMeasurable.integral_prod_right' (ν := μG)
    (f := fun x : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      sv hnm (maskOp x.1 ((Real.sqrt (m:ℝ))⁻¹ • x.2)) i)
    (measurable_masked_singular_pair hnm i).stronglyMeasurable
  exact hh.measurable


lemma measurable_lambdaHat_pair {m n T : ℕ} (hnm : n ≤ m) (i : Fin n) :
    Measurable (fun x : Matrix (Fin m) (Fin n) ℝ × (Fin T → Matrix (Fin m) (Fin n) ℝ) =>
      lambdaHat hnm x.1 x.2 i) := by
  have ht : ∀ t : Fin T, Measurable (fun x : Matrix (Fin m) (Fin n) ℝ ×
      (Fin T → Matrix (Fin m) (Fin n) ℝ) =>
      sv hnm (maskOp x.1 ((Real.sqrt (m:ℝ))⁻¹ • x.2 t)) i) := by
    intro t
    have hp : Measurable (fun x : Matrix (Fin m) (Fin n) ℝ ×
        (Fin T → Matrix (Fin m) (Fin n) ℝ) => (x.1, x.2 t)) :=
      measurable_fst.prodMk ((measurable_pi_apply t).comp measurable_snd)
    simpa only [Function.comp_def] using (measurable_masked_singular_pair (m:=m) (n:=n) hnm i).comp hp
  exact (Finset.measurable_sum _ (fun t _ => ht t)).const_mul ((T:ℝ)⁻¹)


/-- Fixed-mask Monte-Carlo concentration transported through the actual grouped
independence in `IsSamplingLaw`.  The reference Gaussian law is genuine and the
integrability requirement is discharged by the existing finite Gaussian bound. -/
theorem sampling_mc_probability (D : ℝ) (hD : 0 < D) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (m n T : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m) (hT : 1 ≤ T)
        {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Om Hm : Ω → Matrix (Fin m) (Fin n) ℝ)
        (G : Ω → Fin T → Matrix (Fin m) (Fin n) ℝ) (p sigma K : ℝ)
        (hlaw : IsSamplingLaw μ Om Hm G p sigma K)
        (μG : Measure (Matrix (Fin m) (Fin n) ℝ)) [IsProbabilityMeasure μG]
        (hgauss : IsStdGaussianMatrixLaw μG),
        μ {s | ∀ i, |lambdaHat hnm (Om s) (G s) i - lambdaCirc hnm μG (Om s) i|
          ≤ C * Real.sqrt (Real.log (n:ℝ) / ((m:ℝ)*(T:ℝ)))}
          ≥ ENNReal.ofReal (1-c*Real.rpow (n:ℝ) (-D)) := by
  obtain ⟨c,C,hc,hC,hMC⟩ := statopia_math_node_1891546014_cda991f2.{u} D hD
  refine ⟨c,C,hc,hC,?_⟩
  intro m n T hn hnm hT Ω _ μ _ Om Hm G p sigma K hlaw μG _ hgauss
  have hparts := sampling_law_components μ Om Hm G p sigma K hlaw
  have hOm : Measurable Om := measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => hlaw.1 i j))
  have hG : Measurable G := measurable_pi_iff.2 (fun t => measurable_pi_iff.2 (fun i =>
    measurable_pi_iff.2 (fun j => hparts.2.1.1 t i j)))
  let μO := μ.map Om
  let μD := μ.map G
  haveI : IsProbabilityMeasure μO := μ.isProbabilityMeasure_map hOm.aemeasurable
  haveI : IsProbabilityMeasure μD := μ.isProbabilityMeasure_map hG.aemeasurable
  let A : Set (Matrix (Fin m) (Fin n) ℝ × (Fin T → Matrix (Fin m) (Fin n) ℝ)) :=
    {x | ∀ i, |lambdaHat hnm x.1 x.2 i - lambdaCirc hnm μG x.1 i|
      ≤ C * Real.sqrt (Real.log (n:ℝ) / ((m:ℝ)*(T:ℝ)))}
  have hA : MeasurableSet A := by
    simp only [A, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (((measurable_lambdaHat_pair hnm i).sub
      ((measurable_lambdaCirc hnm μG i).comp measurable_fst)).abs) measurable_const
  have hbinaryMeas : MeasurableSet {O : Matrix (Fin m) (Fin n) ℝ | ∀ i j, O i j = 0 ∨ O i j = 1} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    exact (measurableSet_eq_fun ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const).union
      (measurableSet_eq_fun ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const)
  have hbinary : ∀ᵐ O ∂μO, ∀ i j, O i j = 0 ∨ O i j = 1 :=
    (ae_map_iff hOm.aemeasurable hbinaryMeas).2 (ae_of_all μ hparts.1.2.1)
  have hcond : ∀ᵐ O ∂μO,
      ENNReal.ofReal (1-c*Real.rpow (n:ℝ) (-D)) ≤ μD (Prod.mk O ⁻¹' A) := by
    filter_upwards [hbinary] with O hbin
    have hs : MeasurableSet (Prod.mk O ⁻¹' A) := hA.preimage measurable_prodMk_left
    change _ ≤ (μ.map G) (Prod.mk O ⁻¹' A)
    rw [Measure.map_apply hG hs]
    exact hMC m n T hn hnm hT O hbin μG hgauss
      (statopia_math_node_817079420_981e1edb m n hnm O μG hgauss) μ G hparts.2.1
  have hprod : μ.map (fun s => (Om s, G s)) = μO.prod μD :=
    (indepFun_iff_map_prod_eq_prod_map_map hOm.aemeasurable hG.aemeasurable).1 hparts.2.2.1
  calc
    μ {s | ∀ i, |lambdaHat hnm (Om s) (G s) i - lambdaCirc hnm μG (Om s) i|
      ≤ C * Real.sqrt (Real.log (n:ℝ) / ((m:ℝ)*(T:ℝ)))}
        = (μ.map (fun s => (Om s,G s))) A := (Measure.map_apply (hOm.prodMk hG) hA).symm
    _ = (μO.prod μD) A := by rw [hprod]
    _ = ∫⁻ O, μD (Prod.mk O ⁻¹' A) ∂μO := Measure.prod_apply hA
    _ ≥ ∫⁻ _O, ENNReal.ofReal (1-c*Real.rpow (n:ℝ) (-D)) ∂μO := lintegral_mono_ae hcond
    _ = ENNReal.ofReal (1-c*Real.rpow (n:ℝ) (-D)) := by simp

end
#print axioms spectral_calibration_on_good_spectra
#print axioms sampling_law_components
#print axioms sampling_mc_probability
end ResidualLoss20261106.Statlib.Imported

