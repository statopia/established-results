import Statlib.HighDim.MatrixAnalysis.NuclearNormProperties
import Statlib.HighDim.MatrixAnalysis.SvSoftThreshold
import Lean
import ProverJobs.ResidualE2ESupport20261106.M_5fe524fd1f37cd26c86b
import ProverJobs.ResidualE2ESupport20261106.M_000a1d47627029032cac
import ProverJobs.ResidualE2ESupport20261106.M_1b66fe091da8ddacd93f
import ProverJobs.ResidualE2ESupport20261106.M_0a73ccfa17d62d9beed4
import ProverJobs.ResidualE2ESupport20261106.M_8fca21b6c1dec9760fbf
import ProverJobs.ResidualE2ESupport20261106.M_877590d73402328870ca
import ProverJobs.ResidualE2ESupport20261106.M_0633b7602f84256af2fa

namespace PaperProofTasks.ResidualE2ESupport20261106

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ResidualLoss20261106.Statlib.Imported
universe u
noncomputable section
set_option maxHeartbeats 4500000

theorem loss_main_event_all_alpha (K rhoMin : ℝ) (hK : 0 < K) (hrhoMin : 0 < rhoMin) :
    ∀ (alpha0 : ℝ), 15 < alpha0 →
          ∃ c c1 C C0 : ℝ, 0 < c ∧ 0 < c1 ∧ 0 < C ∧ 0 < C0 ∧ ∃ m0 : ℕ,
          ∀ (m n : ℕ) (p : ℝ) (T r : ℕ) (sigma : ℝ)
            {Ωs : Type u} [MeasurableSpace Ωs] (μ : Measure Ωs) [IsProbabilityMeasure μ]
            (Om Hm : Ωs → Matrix (Fin m) (Fin n) ℝ)
            (G : Ωs → Fin T → Matrix (Fin m) (Fin n) ℝ)
            (M0 : Matrix (Fin m) (Fin n) ℝ) (w : Fin n → ℝ)
            (U0 : Matrix (Fin m) (Fin r) ℝ) (d0 : Fin r → ℝ)
            (V0 : Matrix (Fin n) (Fin r) ℝ) (mu0 : ℝ)
            (hsigma : 0 < sigma)
            (hm : m0 ≤ m) (hn : 2 ≤ n) (hnm : n ≤ m)
            (hp0 : 0 < p) (hp1 : p ≤ 1)
            (hrho_lo : rhoMin ≤ rho m n) (hrho_hi : rho m n ≤ 1)
            (hT : 1 ≤ T)
            (hmp : Real.rpow (Real.log (m : ℝ)) alpha0 ≤ (m : ℝ) * p)
            (hw_nn : ∀ i : Fin n, 0 ≤ w i) (hw_sum : (∑ i : Fin n, w i) = 1)
            (hM0 : IsIncoherentSVD M0 U0 d0 V0 mu0)
            (hlaw : IsSamplingLaw μ Om Hm G p sigma K),
              ∃ E : Set Ωs, MeasurableSet E ∧
                ENNReal.ofReal (1 - c1 * ((n : ℝ) ^ 3)⁻¹) ≤ μ E ∧
                ∀ s ∈ E,
                  (Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om s))
                      ≤ C * Real.sqrt ((m : ℝ) / p)) ∧
                  (∀ A B : Matrix (Fin m) (Fin n) ℝ,
                    inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
                      |matInner (TOmega (Om s) U0 V0 A) B - p * matInner A B|
                        ≤ C * Real.sqrt (mu0 * (r : ℝ) * Real.log (m : ℝ) / ((n : ℝ) * p))
                            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A
                            * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B) ∧
                  (∀ i : Fin n,
                    |sv hnm (maskOp (Om s) (Hm s)) i / (sigma * Real.sqrt (m : ℝ))
                      - lambdaHat hnm (Om s) (G s) i|
                      ≤ C * Real.sqrt p * deltaM m) ∧
                  (max (Statlib.HighDim.MatrixAnalysis.opNorm (maskOp (Om s) (Hm s))
                        / (sigma * Real.sqrt (m : ℝ)))
                      (lambdaHat hnm (Om s) (G s)
                        ⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩)
                    ≤ Real.sqrt p * (1 + Real.sqrt (rho m n) + C * deltaM m)) ∧
                  (c * (n : ℝ) * Real.sqrt p
                    ≤ ∑ i ∈ indexSet n, lambdaHat hnm (Om s) (G s) i) ∧
                  (|sigmaHat hnm (indexSet n) (lambdaHat hnm (Om s) (G s))
                        (Yobs (Om s) M0 (Hm s)) (Om s) M0
                      / sigma - 1| ≤ C * deltaM m) ∧
                  (loss hnm (indexSet n) p w (lambdaHat hnm (Om s) (G s))
                      (Yobs (Om s) M0 (Hm s)) (Om s) M0
                    ≤ ENNReal.ofReal (C0 * deltaM m ^ 2)) ∧
                  (∀ M : Matrix (Fin m) (Fin n) ℝ,
                    |sigmaHat hnm (indexSet n) (lambdaHat hnm (Om s) (G s))
                          (Yobs (Om s) M0 (Hm s)) (Om s) M
                        / sigma - 1|
                      ≤ C * deltaM m
                        + C * Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp (Om s) (M - M0))
                            / (sigma * Real.sqrt ((m : ℝ) * (n : ℝ) * p))) := by
  intro alpha0 halpha
  obtain ⟨CI,cI,hCI,hcI,mI,hI⟩ := noise_calibration.{u} K rhoMin hK hrhoMin alpha0 halpha
  obtain ⟨cR,CR,hcR,hCR,mR,hR⟩ := reference_all_alpha.{u} 4 rhoMin (by norm_num) hrhoMin alpha0 halpha
  obtain ⟨cM,CM,hcM,hCM,hMC⟩ := sampling_mc_probability.{u} 4 (by norm_num)
  obtain ⟨CG,cG,hCG,hcG,mG,hG⟩ := statopia_math_node_1222515461_d927f311.{u} alpha0 halpha rhoMin hrhoMin
  let CL := CR+CM
  let edge := Real.pi*rhoMin/12
  let cb := edge/22
  let C1 := CI+CL
  let C4 := C1/cb
  let C := CG+C1+C4+1/cb+1
  have hCL : 0 < CL := add_pos hCR hCM
  have hedge : 0 < edge := by dsimp [edge]; positivity
  have hcb : 0 < cb := div_pos hedge (by norm_num)
  have hC1 : 0 < C1 := add_pos hCI hCL
  have hC4 : 0 < C4 := div_pos hC1 hcb
  have hC : 0 < C := by dsimp [C]; positivity
  have hCGC : CG ≤ C := by
    dsimp only [C]
    linarith only [hC1,hC4,hCG,one_div_pos.mpr hcb]
  have hC1C : C1 ≤ C := by
    dsimp only [C]
    linarith only [hC1,hC4,hCG,one_div_pos.mpr hcb]
  have hC4C : C4 ≤ C := by
    dsimp only [C]
    linarith only [hC1,hC4,hCG,one_div_pos.mpr hcb]
  have hinvC : 1/cb ≤ C := by
    dsimp only [C]
    linarith only [hCG,hC1,hC4]
  have hCIC : CI ≤ C := le_trans (le_add_of_nonneg_right hCL.le) hC1C
  have hCLC : CL ≤ C := le_trans (le_add_of_nonneg_left hCI.le) hC1C
  obtain ⟨mS,hmS3,hS⟩ := calibration_growth_threshold CI CL edge cb hCI hCL hedge hcb
  refine ⟨cb,cG+cI+cR+cM,C,2*C1^2+8*C4^2*3^2,hcb,by positivity,hC,by positivity,
    max mI (max mR (max mG mS)),?_⟩
  intro m n p T r sigma Ωs _ μ _ Om Hm G M0 w U0 d0 V0 mu0 hsigma hm hn hnm hp0 hp1 hrho_lo hrho_hi hT hmp hw_nn hw_sum hM0 hlaw
  have hmI : mI ≤ m := (le_max_left _ _).trans hm
  have hmR : mR ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmG : mG ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hmS : mS ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  obtain ⟨hlog,hsmallI,hsmallL,hsmallC⟩ := hS m hmS
  have hm3 : 3 ≤ m := hmS3.trans hmS
  have hdelta : 0 ≤ deltaM m := by unfold deltaM; exact inv_nonneg.mpr (by linarith only [hlog])
  have hsp := Real.sqrt_nonneg p
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨gamma,hgamma,hgammaUpper,hgammaLower⟩ :=
    (statopia_math_node_2262828856_34ee8798 rhoMin (rho m n) hrhoMin hrho_lo hrho_hi).2.2.2 n hn1
  have hgammaTwo : ∀ i, gamma i ≤ 2 := by
    intro i
    have hs : Real.sqrt (rho m n) ≤ 1 := by simpa using Real.sqrt_le_sqrt hrho_hi
    have hg := hgammaUpper i
    unfold lambdaPlus at hg
    linarith only [hs,hg]
  obtain ⟨μG,hμG,hgauss⟩ := exists_standard_gaussian_matrix_law m n
  letI : IsProbabilityMeasure μG := hμG
  have hparts := sampling_law_components μ Om Hm G p sigma K hlaw
  have hmask := hparts.1
  have hdraws := hparts.2.1
  have hOm := hlaw.1
  have hbin := hlaw.2.1
  have hprob := hlaw.2.2.1
  have hHm := hlaw.2.2.2.1
  have hint := hlaw.2.2.2.2.1
  have hmean := hlaw.2.2.2.2.2.1
  have hint2 := hlaw.2.2.2.2.2.2.1
  have hvar := hlaw.2.2.2.2.2.2.2.1
  have htail := hlaw.2.2.2.2.2.2.2.2.1
  let X := fun i : Fin n => fun s : Ωs => sv hnm (maskOp (Om s) (Hm s)) i / (sigma*Real.sqrt (m:ℝ))
  let L := fun i : Fin n => fun s : Ωs => lambdaHat hnm (Om s) (G s) i
  let R := fun i : Fin n => fun s : Ωs => lambdaCirc hnm μG (Om s) i
  have hOmM : Measurable Om := measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => hOm i j))
  have hGM : Measurable G := measurable_pi_iff.2 (fun t => measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => hdraws.1 t i j)))
  have hXM : ∀ i, Measurable (X i) := by
    intro i
    have hA : Measurable (fun s => maskOp (Om s) (Hm s)) := by
      exact measurable_pi_iff.2 (fun a => measurable_pi_iff.2 (fun b => (hOm a b).mul (hHm a b)))
    exact ((statopia_math_node_3334131066_c2302711 (Fin.castLE (le_min hnm le_rfl) i)).comp hA).div_const _
  have hpair : Measurable (fun s : Ωs => (Om s,G s)) := hOmM.prodMk hGM
  have hLM : ∀ i, Measurable (L i) := by
    intro i
    change Measurable (fun s : Ωs => lambdaHat hnm (Om s) (G s) i)
    simpa only [Function.comp_def] using (measurable_lambdaHat_pair (m:=m) (n:=n) (T:=T) hnm i).comp hpair
  have hRM : ∀ i, Measurable (R i) := by
    intro i
    change Measurable (fun s : Ωs => lambdaCirc hnm μG (Om s) i)
    simpa only [Function.comp_def] using (measurable_lambdaCirc (m:=m) (n:=n) hnm μG i).comp hOmM
  let S : Set Ωs := {s | (Statlib.HighDim.MatrixAnalysis.opNorm (centeredMaskOp p (Om s))
      ≤ CG*Real.sqrt ((m:ℝ)/p)) ∧ ∀ A B : Matrix (Fin m) (Fin n) ℝ,
      inTangentSpace U0 V0 A → inTangentSpace U0 V0 B →
      |matInner (TOmega (Om s) U0 V0 A) B - p*matInner A B|
        ≤ CG*Real.sqrt (mu0*(r:ℝ)*Real.log (m:ℝ)/((n:ℝ)*p))
          * Statlib.HighDim.MatrixAnalysis.frobeniusNorm A * Statlib.HighDim.MatrixAnalysis.frobeniusNorm B}
  let N : Set Ωs := {s | (∀ i, |X i s-Real.sqrt p*gamma i| ≤ CI*Real.sqrt p*deltaM m) ∧
    X ⟨0,Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩ s ≤ Real.sqrt p*(1+Real.sqrt (rho m n)+CI*deltaM m)}
  let V : Set Ωs := {s | ∀ i, |R i s-Real.sqrt p*gamma i| ≤ CR*Real.sqrt p*deltaM m}
  let Q : Set Ωs := {s | ∀ i, |L i s-R i s| ≤ CM*Real.sqrt (Real.log (n:ℝ)/((m:ℝ)*(T:ℝ)))}
  have hSmeas : MeasurableSet S := statopia_math_node_572064251_06b3b28d m n r p CG mu0 U0 V0 Om hOm
  have hNmeas : MeasurableSet N := by
    apply MeasurableSet.inter
    · have hh : MeasurableSet (⋂ i : Fin n, {s : Ωs |
          |X i s-Real.sqrt p*gamma i| ≤ CI*Real.sqrt p*deltaM m}) :=
        MeasurableSet.iInter (fun i => measurableSet_le (((hXM i).sub_const _).abs) measurable_const)
      convert hh using 1
      ext s
      simp only [Set.mem_iInter,Set.mem_setOf_eq]
      rfl
    · exact measurableSet_le (hXM _) measurable_const
  have hVmeas : MeasurableSet V := by
    simp only [V,Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (((hRM i).sub_const _).abs) measurable_const)
  have hQmeas : MeasurableSet Q := by
    simp only [Q,Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (((hLM i).sub (hRM i)).abs) measurable_const)
  have hSprob := hG m n r p μ Om M0 U0 d0 V0 mu0 hmG hn hnm hp0 hp1 hrho_lo hrho_hi hmp hM0 hmask
  have hNprob := hI p sigma n m gamma μ Om Hm hmI hn hnm hp0 hp1 hrho_lo hrho_hi hsigma hmp hgamma
    hOm hbin hprob hHm hint hmean hint2 hvar htail (by
      convert hparts.2.2.2 using 1 <;> first | rfl | (funext x s; cases x <;> rfl))
  have hVprob := hR m n p μ Om μG gamma hmR hn hnm hp0 hp1 hrho_lo hrho_hi hmp hgamma hmask hgauss
  have hQprob := hMC m n T hn hnm hT μ Om Hm G p sigma K hlaw μG hgauss
  have hpow4 : Real.rpow (n:ℝ) (-4:ℝ) = ((n:ℝ)^4)⁻¹ := by
    calc
      _ = (Real.rpow (n:ℝ) (4:ℝ))⁻¹ := Real.rpow_neg hnpos.le 4
      _ = _ := by norm_num
  change ENNReal.ofReal (1-cI*Real.rpow (n:ℝ) (-4:ℝ)) ≤ μ N at hNprob
  change ENNReal.ofReal (1-cM*Real.rpow (n:ℝ) (-4:ℝ)) ≤ μ Q at hQprob
  change ENNReal.ofReal (1-cR*Real.rpow (n:ℝ) (-4:ℝ)) ≤ μ V at hVprob
  change ENNReal.ofReal (1-cG*((n:ℝ)^4)⁻¹) ≤ μ S at hSprob
  rw [← hpow4] at hSprob
  let E := ((S∩N)∩V)∩Q
  refine ⟨E,((hSmeas.inter hNmeas).inter hVmeas).inter hQmeas,?_,?_⟩
  · have hprobE := probability_inter_lower μ ((S∩N)∩V) Q hQmeas
      ((cG*Real.rpow (n:ℝ) (-4)+cI*Real.rpow (n:ℝ) (-4))+cR*Real.rpow (n:ℝ) (-4))
      (cM*Real.rpow (n:ℝ) (-4))
      (probability_inter_lower μ (S∩N) V hVmeas
        (cG*Real.rpow (n:ℝ) (-4)+cI*Real.rpow (n:ℝ) (-4)) (cR*Real.rpow (n:ℝ) (-4))
        (probability_inter_lower μ S N hNmeas _ _ hSprob hNprob) hVprob) hQprob
    apply le_trans (ENNReal.ofReal_mono ?_) hprobE
    have hnbase : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hpow : Real.rpow (n:ℝ) (-4:ℝ) ≤ ((n:ℝ)^3)⁻¹ := by
      calc
        _ ≤ Real.rpow (n:ℝ) (-3:ℝ) := Real.rpow_le_rpow_of_exponent_le hnbase (by norm_num)
        _ = _ := by
          calc
            _ = (Real.rpow (n:ℝ) (3:ℝ))⁻¹ := Real.rpow_neg hnpos.le 3
            _ = _ := by norm_num
    calc
      _ ≤ 1-(cG+cI+cR+cM)*Real.rpow (n:ℝ) (-4:ℝ) :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left hpow (show 0 ≤ cG+cI+cR+cM by positivity)) 1
      _ = _ := by ring
  · intro s hs
    obtain ⟨⟨⟨hsG,hsI⟩,hsR⟩,hsM⟩ := hs
    have hscale := mc_scale_le_logarithmic m n T hn hnm hT p alpha0 hp0.le (by linarith only [halpha]) hlog hmp
    have hLclose : ∀ i, |L i s-Real.sqrt p*gamma i| ≤ CL*Real.sqrt p*deltaM m := by
      intro i
      calc
        _ ≤ |L i s-R i s| + |R i s-Real.sqrt p*gamma i| := abs_sub_le _ _ _
        _ ≤ CM*Real.sqrt (Real.log (n:ℝ)/((m:ℝ)*(T:ℝ))) + CR*Real.sqrt p*deltaM m := add_le_add (hsM i) (hsR i)
        _ ≤ CM*(Real.sqrt p*deltaM m) + CR*Real.sqrt p*deltaM m := add_le_add (mul_le_mul_of_nonneg_left hscale hCM.le) le_rfl
        _ = CL*Real.sqrt p*deltaM m := by dsimp [CL]; ring
    have hfinite := spectral_calibration_on_good_spectra rhoMin hrhoMin m n hn hnm p sigma hp0 hp1 hsigma
      (Om s) M0 (Hm s) (hbin s) gamma (lambdaHat hnm (Om s) (G s)) w hw_nn hw_sum hgammaLower hgammaTwo CI CL
      hCI hCL hsmallI hsmallL hsmallC hsI.1 hLclose
    change (∀ i, |X i s-L i s| ≤ C1*Real.sqrt p*deltaM m) ∧
      (cb*(n:ℝ)*Real.sqrt p ≤ ∑ i ∈ indexSet n, L i s) ∧
      |sigmaHat hnm (indexSet n) (lambdaHat hnm (Om s) (G s)) (Yobs (Om s) M0 (Hm s)) (Om s) M0 / sigma-1| ≤ C4*deltaM m ∧
      loss hnm (indexSet n) p w (lambdaHat hnm (Om s) (G s)) (Yobs (Om s) M0 (Hm s)) (Om s) M0 ≤ ENNReal.ofReal ((2*C1^2+8*C4^2*3^2)*deltaM m^2) ∧
      (∀ M, |sigmaHat hnm (indexSet n) (lambdaHat hnm (Om s) (G s)) (Yobs (Om s) M0 (Hm s)) (Om s) M / sigma-1|
        ≤ C4*deltaM m+(1/cb)*Statlib.HighDim.MatrixAnalysis.frobeniusNorm (maskOp (Om s) (M-M0)) / (sigma*Real.sqrt ((m:ℝ)*(n:ℝ)*p))) at hfinite
    refine ⟨hsG.1.trans (mul_le_mul_of_nonneg_right hCGC (Real.sqrt_nonneg _)),?_,?_,?_,hfinite.2.1,?_,hfinite.2.2.2.1,?_⟩
    · intro A B hA hB
      apply (hsG.2 A B hA hB).trans
      apply mul_le_mul_of_nonneg_right _ (by unfold Statlib.HighDim.MatrixAnalysis.frobeniusNorm; positivity)
      apply mul_le_mul_of_nonneg_right _ (by unfold Statlib.HighDim.MatrixAnalysis.frobeniusNorm; positivity)
      exact mul_le_mul_of_nonneg_right hCGC (Real.sqrt_nonneg _)
    · intro i
      exact (hfinite.1 i).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1C hsp) hdelta)
    · apply max_le
      · rw [← sv_zero_eq_opNorm hnm (by omega : 0 < n) (maskOp (Om s) (Hm s))]
        exact hsI.2.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCIC hdelta)) hsp)
      · have hLtop := (abs_le.mp (hLclose ⟨0,Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩)).2
        have hgtop := mul_le_mul_of_nonneg_left (hgammaUpper ⟨0,Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hn⟩) hsp
        have hmon := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCLC hdelta) hsp
        unfold lambdaPlus at hgtop
        change L _ s ≤ _
        linarith only [hLtop,hgtop,hmon]
    · exact hfinite.2.2.1.trans (mul_le_mul_of_nonneg_right hC4C hdelta)
    · intro M
      apply (hfinite.2.2.2.2 M).trans
      apply add_le_add (mul_le_mul_of_nonneg_right hC4C hdelta)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hinvC (by unfold Statlib.HighDim.MatrixAnalysis.frobeniusNorm; positivity)

end
end ResidualLoss20261106.Statlib.Imported
#print axioms ResidualLoss20261106.Statlib.Imported.loss_main_event_all_alpha

