import Statlib.HighDim.CovarianceMatrix.SampleCovariance
import Statlib.StatFoundation.Vocabulary.OrliczNorm
import Lean
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.ExternalNodes.Node_5fcc0b8e12b9479c98ea
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.ExternalNodes.Node_87ee2dee4bb04055bcd1
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.ExternalNodes.Node_a63e0b3e27c74b69bca4
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.ExternalNodes.Node_a6ef5db72938484aba23
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.ExternalNodes.Node_e0c7bc723f0f457796b6
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Vocabulary
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.ProvedNodes
import ProverJobs.job_paper_106ef041a01147028d56a10b8f69010e.Base

namespace PaperProofTasks.job_paper_106ef041a01147028d56a10b8f69010e

namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
open MeasureTheory ProbabilityTheory
noncomputable section

theorem paper_106ef041a01147028d56a10b8f69010e
    (c : ℝ) (hc : 0 < c) (q : ℕ) (hq : 1 ≤ q)
    (L Leps : ℝ) (hL : 0 < L) (hLeps : 0 < Leps) :
    ∃ Cx Cdelta CH Cd Ceps N0 : ℝ,
      0 < Cx ∧ 0 < Cdelta ∧ 0 < CH ∧ 0 < Cd ∧ 0 < Ceps ∧ 0 < N0 ∧
        (∀ (p : ℕ), 2 ≤ p → ∀ (K : ℕ), 1 ≤ K →
          ∀ (Ω : Type) [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
            (Prow : Measure ((Fin p → ℝ) × (Fin q → ℝ))) [IsProbabilityMeasure Prow]
            (f : (Fin q → ℝ) → (Fin p → ℝ)), Measurable f →
          (∀ i j, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
              (f x.2 i + x.1 i) * (f x.2 j + x.1 j)) Prow) →
          ∀ (SigmaX : Fin p → Fin p → ℝ),
            (∀ i j, SigmaX i j
              = ∫ x : (Fin p → ℝ) × (Fin q → ℝ),
                  (f x.2 i + x.1 i) * (f x.2 j + x.1 j) ∂Prow) →
          (∀ i j, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
              (f x.2 i + x.1 i) * x.2 j) Prow) →
          ∀ (M : Fin p → Fin q → ℝ),
            (∀ i j, M i j
              = ∫ x : (Fin p → ℝ) × (Fin q → ℝ), (f x.2 i + x.1 i) * x.2 j ∂Prow) →
          (∀ i, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i) Prow) →
          (∀ i, ∫ x : (Fin p → ℝ) × (Fin q → ℝ), x.1 i ∂Prow = 0) →
          (∀ j, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j) Prow) →
          (∀ j, ∫ x : (Fin p → ℝ) × (Fin q → ℝ), x.2 j ∂Prow = 0) →
          (∀ i, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i) Prow) →
          (∀ i, ∫ x : (Fin p → ℝ) × (Fin q → ℝ), f x.2 i ∂Prow = 0) →
          (∀ i, HasSubgaussianMGF (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
            ⟨L, hL.le⟩ Prow) →
          (∀ j, HasSubgaussianMGF (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
            ⟨L, hL.le⟩ Prow) →
          (∀ i, HasSubgaussianMGF (fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i)
            ⟨L, hL.le⟩ Prow) →
          (∀ i j, Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i * x.2 j) Prow) →
          (∀ i j, ∫ x : (Fin p → ℝ) × (Fin q → ℝ), x.1 i * x.2 j ∂Prow = 0) →
          ∀ (nt : ℕ) (hnt : 0 < nt) (ns : Fin K → ℕ) (hns : ∀ k, 0 < ns k)
            (nsTot : ℝ) (hnsTot : nsTot = ∑ k : Fin K, (ns k : ℝ)),
          ∀ (betat : Fin p → ℝ) (betas : Fin K → Fin p → ℝ)
            (phit : Fin q → ℝ) (phis : Fin K → Fin q → ℝ),
          ∀ (sEta : ℕ) (hsEta : sEta ≤ p) (sDelta Cphi Bphi : ℝ) (hsDelta : 0 ≤ sDelta)
            (hCphi : 0 < Cphi) (hBphi : 0 < Bphi),
          l2norm (phiBar ns nsTot phis - phit) ≤ Cphi * aTcoef p nt →
          (∀ k, l2norm (phis k - phit) ≤ Bphi) →
          (∀ k, ∑ j : Fin p, |betas k j - betaBar ns nsTot betas j| ≤ sDelta) →
          (Finset.univ.filter (fun j : Fin p => eta0Vec ns nsTot betat betas j ≠ 0)).card ≤ sEta →
          ∀ (Et : Fin nt → Ω → Fin p → ℝ) (Ht : Fin nt → Ω → Fin q → ℝ)
            (epsT : Fin nt → Ω → ℝ)
            (Es : (k : Fin K) → Fin (ns k) → Ω → Fin p → ℝ)
            (Hs : (k : Fin K) → Fin (ns k) → Ω → Fin q → ℝ)
            (epsS : (k : Fin K) → Fin (ns k) → Ω → ℝ)
            (sigmaSq : ℝ) (hsigmaSq : 0 ≤ sigmaSq),
          (∀ r, Measurable (Et r)) → (∀ r, Measurable (Ht r)) →
          (∀ r, Measurable (epsT r)) → (∀ k r, Measurable (Es k r)) →
          (∀ k r, Measurable (Hs k r)) → (∀ k r, Measurable (epsS k r)) →
          (∀ r, Measure.map (fun ω => (Et r ω, Ht r ω)) mu = Prow) →
          (∀ k r, Measure.map (fun ω => (Es k r ω, Hs k r ω)) mu = Prow) →
          iIndepFun (pooledRow Et Ht epsT Es Hs epsS) mu →
          (∀ r, IndepFun (epsT r) (fun ω => (Et r ω, Ht r ω)) mu) →
          (∀ k r, IndepFun (epsS k r) (fun ω => (Es k r ω, Hs k r ω)) mu) →
          (∀ r, Integrable (fun ω => epsT r ω) mu) →
          (∀ k r, Integrable (fun ω => epsS k r ω) mu) →
          (∀ r, ∫ ω, epsT r ω ∂mu = 0) → (∀ k r, ∫ ω, epsS k r ω ∂mu = 0) →
          (∀ r, Integrable (fun ω => (epsT r ω) ^ 2) mu) →
          (∀ k r, Integrable (fun ω => (epsS k r ω) ^ 2) mu) →
          (∀ r, ∫ ω, (epsT r ω) ^ 2 ∂mu = sigmaSq) →
          (∀ k r, ∫ ω, (epsS k r ω) ^ 2 ∂mu = sigmaSq) →
          (∀ r, HasSubgaussianMGF (epsT r) ⟨Leps, hLeps.le⟩ mu) →
          (∀ k r, HasSubgaussianMGF (epsS k r) ⟨Leps, hLeps.le⟩ mu) →
                  (nt : ℝ) ≤ nsTot → N0 * Real.log (p : ℝ) ≤ (nt : ℝ) →
                    1 - Real.rpow (p : ℝ) (-c) ≤
                        mu.real (Gset f Et Ht epsT Es Hs epsS SigmaX M betas phit phis nsTot
                          Cx Cdelta CH Cd Ceps sDelta Bphi) ∧
                      (∀ ω : Ω, ω ∈ Gset f Et Ht epsT Es Hs epsS SigmaX M betas phit phis nsTot
                          Cx Cdelta CH Cd Ceps sDelta Bphi →
                        MatSupLe (fun i j =>
                            (∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * (f (Ht r ω) j + Et r ω j))
                              / (nt : ℝ) - SigmaX i j) (Cx * aTcoef p nt) ∧
                        MatSupLe (fun i j =>
                            (∑ k : Fin K, ∑ r : Fin (ns k),
                              (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j))
                              / nsTot - SigmaX i j) (Cx * aSCoef p nsTot)))
:= by
  /- @proof-region region.root.3206ac050fd2 begin -/
  have hL' : 0 < max L 1 := lt_of_lt_of_le one_pos (le_max_right L 1)
  have hLnn : (0 : NNReal) < ⟨max L 1, hL'.le⟩ := by
    rw [← NNReal.coe_lt_coe]
    simpa using hL'
  have hLnn' : (0 : NNReal) < ⟨L, hL.le⟩ := by
    rw [← NNReal.coe_lt_coe]
    simpa using hL
  have hsqrtL : 0 < Real.sqrt L := by
    nlinarith [Real.sq_sqrt hL.le, Real.sqrt_nonneg L, hL]
  have hparamNN : Real.toNNReal ((Real.sqrt L) ^ 2) = ⟨L, hL.le⟩ := by
    apply NNReal.coe_inj.mp
    rw [Real.coe_toNNReal _ (sq_nonneg _), Real.sq_sqrt hL.le]
    simp
  obtain ⟨Cx, hCx, Nx, hNx, _h1⟩ :=
    PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.paper_4a6904a098fa4fcebf3058bbb4e15c0e
      q hq (Real.sqrt L) hsqrtL c hc
  obtain ⟨Cdelta, Ndelta, hCdelta, hNdelta, _h2⟩ :=
    PaperProofTasks.job_paper_8d45c5e7199146b78778677b2fbc23cf.Statlib.Imported.paper_8d45c5e7199146b78778677b2fbc23cf.{0}
      q hq ⟨L, hL.le⟩ hLnn' (8 * max L 1) (by linarith) c hc
  obtain ⟨CH, NH, hCH, hNH, _h3⟩ :=
    PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.paper_6ff987a9c5974b249aed2ac5c2c60b28.{0}
      q hq (4 * (L + 1)) (by linarith) c hc
  obtain ⟨Cd, Nd, hCd, hNd, _h4⟩ :=
    PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.paper_110bb96e917848c19df0625891303d5c.{0}
      ⟨L, hL.le⟩ hLnn' c hc
  obtain ⟨Ceps, Neps, hCeps, hNeps, _h5⟩ :=
    PaperProofTasks.job_paper_5bfd1842871e4bc6b291fb4a9624d4b1.Statlib.Imported.paper_5bfd1842871e4bc6b291fb4a9624d4b1.{0}
      q hq ⟨L, hL.le⟩ ⟨Leps, hLeps.le⟩ c hc
  have hN0pos : 0 < Nx + Ndelta + NH + Nd + Neps + 1 := by linarith
  refine ⟨Cx, Cdelta, CH, Cd, Ceps, Nx + Ndelta + NH + Nd + Neps + 1, hCx, hCdelta, hCH, hCd,
    hCeps, hN0pos, ?_⟩
  intro p hp K hK Ω _ mu _ Prow _ f hf hIntX SigmaX hSigmaX hIntXH M hM hIntE hE0 hIntH hH0
    hIntf hf0 hSgE hSgH hSgf hIntEH hEH0 nt hnt ns hns nsTot hnsTot betat betas phit phis sEta
    hsEta sDelta Cphi Bphi hsDelta hCphi hBphi hphiBar hphik hbeta hEta Et Ht epsT Es Hs epsS
    sigmaSq hsigmaSq hEtm hHtm hepsTm hEsm hHsm hepsSm hmapT hmapS hInd hIndepT hIndepS
    hIntEpsT hIntEpsS hEpsT0 hEpsS0 hIntEpsT2 hIntEpsS2 hEpsT2 hEpsS2 hSgEpsT hSgEpsS hntS hN0
  refine ⟨?_, fun ω hω => ?_⟩
  · have hp1 : (1 : ℝ) < (p : ℝ) := by
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    have hns_pos : ∀ k : Fin K, (0 : ℝ) < (ns k : ℝ) := fun k => by
      exact_mod_cast hns k
    have hnsTot_pos : 0 < nsTot := by
      haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
      rw [hnsTot]
      exact Finset.sum_pos (fun k _ => hns_pos k) Finset.univ_nonempty
    have hx_nonneg : 0 ≤ (p : ℝ).rpow (-c) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hunion : ∀ (S : Fin 10 → Set Ω), (∀ j, MeasurableSet (S j)) →
        (∀ j, mu.real ((S j)ᶜ) ≤ (p : ℝ).rpow (-c) / 20) →
        1 - (p : ℝ).rpow (-c) ≤ mu.real (⋂ j, S j) := by
      intro S hS hbad
      have hmain := statopia_math_node_750611871_04cdf965 Ω mu (Fin 10)
        ((p : ℝ).rpow (-c) / 20)
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (by norm_num)) S hS hbad
      have hcard : ((Fintype.card (Fin 10) : ℕ) : ℝ) = 10 := by norm_num
      rw [hcard] at hmain
      have hstep : 1 - (p : ℝ).rpow (-c) ≤ 1 - 10 * ((p : ℝ).rpow (-c) / 20) := by
        linarith
      linarith [hmain.2]
    have hnsTot_ne : nsTot ≠ 0 := ne_of_gt hnsTot_pos
    have hpool : ((∑ k : Fin K, ns k) : ℝ) = nsTot := by
      rw [hnsTot]
    have hp0 : 0 < p := by omega
    have hq0 : 0 < q := by omega
    have hMf : ∀ (i : Fin p) (j : Fin q),
        M i j = ∫ x : (Fin p → ℝ) × (Fin q → ℝ), f x.2 i * x.2 j ∂Prow :=
      statopia_math_node_1900557282_1188bc25 p q hp0 hq0 Prow f M hM hIntXH hIntEH hEH0
    have haT_nonneg : 0 ≤ aTcoef p nt := by
      rw [aTcoef]; exact Real.sqrt_nonneg _
    have haS_nonneg : 0 ≤ aSCoef p nsTot := by
      rw [aSCoef]; exact Real.sqrt_nonneg _
    have hpool' : ((∑ k : Fin K, ns k : ℕ) : ℝ) = nsTot := by
      push_cast
      exact hpool
    have haS_eq : aSCoef p nsTot
        = Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ)) := by
      rw [aSCoef, hpool']
    have hnt_pos : (0 : ℝ) < (nt : ℝ) := by exact_mod_cast hnt
    have hns_ne : ∀ k : Fin K, (ns k : ℝ) ≠ 0 := fun k => ne_of_gt (hns_pos k)
    have hthresh : ∀ N' : ℝ, N' ≤ Nx + Ndelta + NH + Nd + Neps + 1 →
        N' * Real.log (p : ℝ) ≤ (nt : ℝ) := by
      intro N' hN'
      have hle := mul_le_mul_of_nonneg_right hN' hlogp.le
      linarith [hle, hN0]
    have hNx_le : Nx * Real.log (p : ℝ) ≤ (nt : ℝ) := hthresh Nx (by linarith)
    have hNdelta_le : Ndelta * Real.log (p : ℝ) ≤ (nt : ℝ) := hthresh Ndelta (by linarith)
    have hNH_le : NH * Real.log (p : ℝ) ≤ (nt : ℝ) := hthresh NH (by linarith)
    have hNd_le : Nd * Real.log (p : ℝ) ≤ (nt : ℝ) := hthresh Nd (by linarith)
    have hNeps_le : Neps * Real.log (p : ℝ) ≤ (nt : ℝ) := hthresh Neps (by linarith)
    have hNx_leS : Nx * Real.log (p : ℝ) ≤ nsTot := le_trans hNx_le hntS
    have hNdelta_leS : Ndelta * Real.log (p : ℝ) ≤ nsTot := le_trans hNdelta_le hntS
    have hNH_leS : NH * Real.log (p : ℝ) ≤ nsTot := le_trans hNH_le hntS
    have hNd_leS : Nd * Real.log (p : ℝ) ≤ nsTot := le_trans hNd_le hntS
    have hNeps_leS : Neps * Real.log (p : ℝ) ≤ nsTot := le_trans hNeps_le hntS
    haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
    have hpoolN_pos : 0 < (∑ k : Fin K, ns k : ℕ) :=
      Finset.sum_pos (fun k _ => hns k) Finset.univ_nonempty
    have hnt_le_pool : nt ≤ ∑ k : Fin K, ns k := by
      have h1 : (nt : ℝ) ≤ ((∑ k : Fin K, ns k : ℕ) : ℝ) := by
        rw [hpool']
        exact hntS
      exact_mod_cast h1
    have hcompl : ∀ (S : Set Ω), MeasurableSet S →
        1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S →
        mu.real Sᶜ ≤ (p : ℝ).rpow (-c) / 20 := by
      intro S hS hle
      rw [MeasureTheory.measureReal_compl hS]
      have huniv : mu.real Set.univ = 1 := by simp
      linarith
    have hfinal : ∀ (S : Fin 10 → Set Ω), (∀ j, MeasurableSet (S j)) →
        (∀ j, mu.real ((S j)ᶜ) ≤ (p : ℝ).rpow (-c) / 20) →
        (⋂ j, S j) ⊆ Gset f Et Ht epsT Es Hs epsS SigmaX M betas phit phis nsTot
          Cx Cdelta CH Cd Ceps sDelta Bphi →
        1 - (p : ℝ).rpow (-c) ≤
          mu.real (Gset f Et Ht epsT Es Hs epsS SigmaX M betas phit phis nsTot
            Cx Cdelta CH Cd Ceps sDelta Bphi) := by
      intro S hS hbad hsub
      have h1 := hunion S hS hbad
      have hmono : mu.real (⋂ j, S j) ≤
          mu.real (Gset f Et Ht epsT Es Hs epsS SigmaX M betas phit phis nsTot
            Cx Cdelta CH Cd Ceps sDelta Bphi) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      linarith
    have hEcoord : ∀ (r : Fin nt) (i : Fin p), Measurable (fun ω => Et r ω i) :=
      fun r i => (measurable_pi_apply i).comp (hEtm r)
    have hHcoord : ∀ (r : Fin nt) (j : Fin q), Measurable (fun ω => Ht r ω j) :=
      fun r j => (measurable_pi_apply j).comp (hHtm r)
    have hEscoord : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p), Measurable (fun ω => Es k r ω i) :=
      fun k r i => (measurable_pi_apply i).comp (hEsm k r)
    have hHscoord : ∀ (k : Fin K) (r : Fin (ns k)) (j : Fin q), Measurable (fun ω => Hs k r ω j) :=
      fun k r j => (measurable_pi_apply j).comp (hHsm k r)
    have hfHtcoord : ∀ (r : Fin nt) (i : Fin p), Measurable (fun ω => f (Ht r ω) i) :=
      fun r i => (measurable_pi_apply i).comp (hf.comp (hHtm r))
    have hfHscoord : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        Measurable (fun ω => f (Hs k r ω) i) :=
      fun k r i => (measurable_pi_apply i).comp (hf.comp (hHsm k r))
    have hXtcoord : ∀ (r : Fin nt) (i : Fin p), Measurable (fun ω => f (Ht r ω) i + Et r ω i) :=
      fun r i => (hfHtcoord r i).add (hEcoord r i)
    have hXscoord : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        Measurable (fun ω => f (Hs k r ω) i + Es k r ω i) :=
      fun k r i => (hfHscoord k r i).add (hEscoord k r i)
    have hXtprod : ∀ (r : Fin nt) (i j : Fin p),
        Measurable (fun ω => (f (Ht r ω) i + Et r ω i) * (f (Ht r ω) j + Et r ω j)) :=
      fun r i j => (hXtcoord r i).mul (hXtcoord r j)
    have hXtprodH : ∀ (r : Fin nt) (i : Fin p) (j : Fin q),
        Measurable (fun ω => f (Ht r ω) i * Ht r ω j) :=
      fun r i j => (hfHtcoord r i).mul (hHcoord r j)
    have hEtprodH : ∀ (r : Fin nt) (i : Fin p) (j : Fin q),
        Measurable (fun ω => Et r ω i * Ht r ω j) :=
      fun r i j => (hEcoord r i).mul (hHcoord r j)
    have hXtEps : ∀ (r : Fin nt) (i : Fin p),
        Measurable (fun ω => (f (Ht r ω) i + Et r ω i) * epsT r ω) :=
      fun r i => (hXtcoord r i).mul (hepsTm r)
    have hXsprod : ∀ (k : Fin K) (r : Fin (ns k)) (i j : Fin p),
        Measurable (fun ω => (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j)) :=
      fun k r i j => (hXscoord k r i).mul (hXscoord k r j)
    have hXsprodH : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p) (j : Fin q),
        Measurable (fun ω => f (Hs k r ω) i * Hs k r ω j) :=
      fun k r i j => (hfHscoord k r i).mul (hHscoord k r j)
    have hEsprodH : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p) (j : Fin q),
        Measurable (fun ω => Es k r ω i * Hs k r ω j) :=
      fun k r i j => (hEscoord k r i).mul (hHscoord k r j)
    have hXsEps : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        Measurable (fun ω => (f (Hs k r ω) i + Es k r ω i) * epsS k r ω) :=
      fun k r i => (hXscoord k r i).mul (hepsSm k r)
    have hpairTm : ∀ r : Fin nt, Measurable (fun ω => (Et r ω, Ht r ω)) :=
      fun r => (hEtm r).prod (hHtm r)
    have hpairSm : ∀ (k : Fin K) (r : Fin (ns k)),
        Measurable (fun ω => (Es k r ω, Hs k r ω)) :=
      fun k r => (hEsm k r).prod (hHsm k r)
    have hIntE_mu : ∀ (r : Fin nt) (i : Fin p), Integrable (fun ω => Et r ω i) mu := by
      intro r i
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Et r ω, Ht r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
        (by rw [hmapT r]; exact (hIntE i).1)
        (hpairTm r).aemeasurable).mp (by rw [hmapT r]; exact hIntE i)
    have hIntH_mu : ∀ (r : Fin nt) (j : Fin q), Integrable (fun ω => Ht r ω j) mu := by
      intro r j
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Et r ω, Ht r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
        (by rw [hmapT r]; exact (hIntH j).1)
        (hpairTm r).aemeasurable).mp (by rw [hmapT r]; exact hIntH j)
    have hIntfH_mu : ∀ (r : Fin nt) (i : Fin p), Integrable (fun ω => f (Ht r ω) i) mu := by
      intro r i
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Et r ω, Ht r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i)
        (by rw [hmapT r]; exact (hIntf i).1)
        (hpairTm r).aemeasurable).mp (by rw [hmapT r]; exact hIntf i)
    have hIntEs_mu : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        Integrable (fun ω => Es k r ω i) mu := by
      intro k r i
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Es k r ω, Hs k r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
        (by rw [hmapS k r]; exact (hIntE i).1)
        (hpairSm k r).aemeasurable).mp (by rw [hmapS k r]; exact hIntE i)
    have hIntHs_mu : ∀ (k : Fin K) (r : Fin (ns k)) (j : Fin q),
        Integrable (fun ω => Hs k r ω j) mu := by
      intro k r j
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Es k r ω, Hs k r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
        (by rw [hmapS k r]; exact (hIntH j).1)
        (hpairSm k r).aemeasurable).mp (by rw [hmapS k r]; exact hIntH j)
    have hIntfHs_mu : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        Integrable (fun ω => f (Hs k r ω) i) mu := by
      intro k r i
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Es k r ω, Hs k r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i)
        (by rw [hmapS k r]; exact (hIntf i).1)
        (hpairSm k r).aemeasurable).mp (by rw [hmapS k r]; exact hIntf i)
    have hE0_mu : ∀ (r : Fin nt) (i : Fin p), ∫ ω, Et r ω i ∂mu = 0 := by
      intro r i
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Et r ω, Ht r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
        (hpairTm r).aemeasurable
        ((measurable_pi_apply i).comp measurable_fst).aestronglyMeasurable
      rw [hmapT r] at h
      exact h.symm.trans (hE0 i)
    have hH0_mu : ∀ (r : Fin nt) (j : Fin q), ∫ ω, Ht r ω j ∂mu = 0 := by
      intro r j
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Et r ω, Ht r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
        (hpairTm r).aemeasurable
        ((measurable_pi_apply j).comp measurable_snd).aestronglyMeasurable
      rw [hmapT r] at h
      exact h.symm.trans (hH0 j)
    have hfH0_mu : ∀ (r : Fin nt) (i : Fin p), ∫ ω, f (Ht r ω) i ∂mu = 0 := by
      intro r i
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Et r ω, Ht r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i)
        (hpairTm r).aemeasurable
        ((measurable_pi_apply i).comp (hf.comp measurable_snd)).aestronglyMeasurable
      rw [hmapT r] at h
      exact h.symm.trans (hf0 i)
    have hEs0_mu : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p), ∫ ω, Es k r ω i ∂mu = 0 := by
      intro k r i
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Es k r ω, Hs k r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
        (hpairSm k r).aemeasurable
        ((measurable_pi_apply i).comp measurable_fst).aestronglyMeasurable
      rw [hmapS k r] at h
      exact h.symm.trans (hE0 i)
    have hHs0_mu : ∀ (k : Fin K) (r : Fin (ns k)) (j : Fin q), ∫ ω, Hs k r ω j ∂mu = 0 := by
      intro k r j
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Es k r ω, Hs k r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
        (hpairSm k r).aemeasurable
        ((measurable_pi_apply j).comp measurable_snd).aestronglyMeasurable
      rw [hmapS k r] at h
      exact h.symm.trans (hH0 j)
    have hfHs0_mu : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        ∫ ω, f (Hs k r ω) i ∂mu = 0 := by
      intro k r i
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Es k r ω, Hs k r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i)
        (hpairSm k r).aemeasurable
        ((measurable_pi_apply i).comp (hf.comp measurable_snd)).aestronglyMeasurable
      rw [hmapS k r] at h
      exact h.symm.trans (hf0 i)
    have hidentT : ∀ (i j : Fin nt),
        IdentDistrib (fun ω => (Et i ω, Ht i ω)) (fun ω => (Et j ω, Ht j ω)) mu mu := by
      intro i j
      refine ⟨(hpairTm i).aemeasurable, (hpairTm j).aemeasurable, ?_⟩
      rw [hmapT i, hmapT j]
    have hidentS : ∀ (x y : (k : Fin K) × Fin (ns k)),
        IdentDistrib (fun ω => (Es x.1 x.2 ω, Hs x.1 x.2 ω))
          (fun ω => (Es y.1 y.2 ω, Hs y.1 y.2 ω)) mu mu := by
      intro x y
      refine ⟨(hpairSm x.1 x.2).aemeasurable, (hpairSm y.1 y.2).aemeasurable, ?_⟩
      rw [hmapS x.1 x.2, hmapS y.1 y.2]
    have hSgE_mu : ∀ (r : Fin nt) (i : Fin p),
        HasSubgaussianMGF (fun ω => Et r ω i) ⟨L, hL.le⟩ mu := by
      intro r i
      exact ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun ω => (Et r ω, Ht r ω))
        (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
        (hpairTm r).aemeasurable (by rw [hmapT r]; exact hSgE i)
    have hSgH_mu : ∀ (r : Fin nt) (j : Fin q),
        HasSubgaussianMGF (fun ω => Ht r ω j) ⟨L, hL.le⟩ mu := by
      intro r j
      exact ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun ω => (Et r ω, Ht r ω))
        (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
        (hpairTm r).aemeasurable (by rw [hmapT r]; exact hSgH j)
    have hSgfH_mu : ∀ (r : Fin nt) (i : Fin p),
        HasSubgaussianMGF (fun ω => f (Ht r ω) i) ⟨L, hL.le⟩ mu := by
      intro r i
      exact ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun ω => (Et r ω, Ht r ω))
        (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i)
        (hpairTm r).aemeasurable (by rw [hmapT r]; exact hSgf i)
    have hSgEs_mu : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        HasSubgaussianMGF (fun ω => Es k r ω i) ⟨L, hL.le⟩ mu := by
      intro k r i
      exact ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun ω => (Es k r ω, Hs k r ω))
        (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
        (hpairSm k r).aemeasurable (by rw [hmapS k r]; exact hSgE i)
    have hSgHs_mu : ∀ (k : Fin K) (r : Fin (ns k)) (j : Fin q),
        HasSubgaussianMGF (fun ω => Hs k r ω j) ⟨L, hL.le⟩ mu := by
      intro k r j
      exact ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun ω => (Es k r ω, Hs k r ω))
        (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
        (hpairSm k r).aemeasurable (by rw [hmapS k r]; exact hSgH j)
    have hSgfHs_mu : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p),
        HasSubgaussianMGF (fun ω => f (Hs k r ω) i) ⟨L, hL.le⟩ mu := by
      intro k r i
      exact ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun ω => (Es k r ω, Hs k r ω))
        (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 i)
        (hpairSm k r).aemeasurable (by rw [hmapS k r]; exact hSgf i)
    have hIntEH_mu : ∀ (r : Fin nt) (i : Fin p) (j : Fin q),
        Integrable (fun ω => Et r ω i * Ht r ω j) mu := by
      intro r i j
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Et r ω, Ht r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i * x.2 j)
        (by rw [hmapT r]; exact (hIntEH i j).1)
        (hpairTm r).aemeasurable).mp (by rw [hmapT r]; exact hIntEH i j)
    have hEH0_mu : ∀ (r : Fin nt) (i : Fin p) (j : Fin q),
        ∫ ω, Et r ω i * Ht r ω j ∂mu = 0 := by
      intro r i j
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Et r ω, Ht r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i * x.2 j)
        (hpairTm r).aemeasurable
        ((((measurable_pi_apply i).comp measurable_fst).mul
          ((measurable_pi_apply j).comp measurable_snd))).aestronglyMeasurable
      rw [hmapT r] at h
      exact h.symm.trans (hEH0 i j)
    have hIntEH_muS : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p) (j : Fin q),
        Integrable (fun ω => Es k r ω i * Hs k r ω j) mu := by
      intro k r i j
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Es k r ω, Hs k r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i * x.2 j)
        (by rw [hmapS k r]; exact (hIntEH i j).1)
        (hpairSm k r).aemeasurable).mp (by rw [hmapS k r]; exact hIntEH i j)
    have hEH0_muS : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p) (j : Fin q),
        ∫ ω, Es k r ω i * Hs k r ω j ∂mu = 0 := by
      intro k r i j
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Es k r ω, Hs k r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i * x.2 j)
        (hpairSm k r).aemeasurable
        ((((measurable_pi_apply i).comp measurable_fst).mul
          ((measurable_pi_apply j).comp measurable_snd))).aestronglyMeasurable
      rw [hmapS k r] at h
      exact h.symm.trans (hEH0 i j)
    let S1 : Set Ω := {ω : Ω | ∀ (i j : Fin p), |(∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * (f (Ht r ω) j + Et r ω j)) / (nt : ℝ) - SigmaX i j| ≤ Cx * aTcoef p nt}
    let S2 : Set Ω := {ω : Ω | ∀ (i j : Fin p), |(∑ k : Fin K, ∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j)) / nsTot - SigmaX i j| ≤ Cx * aSCoef p nsTot}
    let S3 : Set Ω := {ω : Ω | ∀ (i : Fin p), |(∑ k : Fin K, (ns k : ℝ) * ∑ j : Fin p, ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j)) / (ns k : ℝ) - SigmaX i j) * (betas k j - betaBar ns nsTot betas j)) / nsTot| ≤ Cdelta * sDelta * aSCoef p nsTot}
    let S4 : Set Ω := {ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, ((∑ r : Fin nt, f (Ht r ω) i * Ht r ω j) / (nt : ℝ) - M i j) ^ 2) ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (nt : ℝ))}
    let S5 : Set Ω := {ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, ((∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i * Hs k r ω j) / nsTot - M i j) ^ 2) ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot)}
    let S6 : Set Ω := {ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, ((∑ r : Fin nt, Et r ω i * Ht r ω j) / (nt : ℝ)) ^ 2) ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (nt : ℝ))}
    let S7 : Set Ω := {ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, ((∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i * Hs k r ω j) / nsTot) ^ 2) ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot)}
    let S8 : Set Ω := {ω : Ω | ∀ (i : Fin p), |(∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * epsT r ω) / (nt : ℝ)| ≤ Ceps * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ))}
    let S9 : Set Ω := {ω : Ω | ∀ (i : Fin p), |(∑ k : Fin K, ∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * epsS k r ω) / nsTot| ≤ Ceps * Real.sqrt (Real.log (p : ℝ) / nsTot)}
    let S10 : Set Ω := {ω : Ω | ∀ (i : Fin p), |(∑ k : Fin K, ∑ j : Fin q, ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * Hs k r ω j) - (ns k : ℝ) * M i j) * (phis k j - phit j)) / nsTot| ≤ Cd * Bphi * Real.sqrt (q : ℝ) * aSCoef p nsTot}
    let A : ℕ → Set Ω := fun n =>
      match n with
      | 0 => S1
      | 1 => S2
      | 2 => S3
      | 3 => S4
      | 4 => S5
      | 5 => S6
      | 6 => S7
      | 7 => S8
      | 8 => S9
      | _ => S10
    let S : Fin 10 → Set Ω := fun j => A j.val
    have hsub : (⋂ j : Fin 10, S j) ⊆ Gset f Et Ht epsT Es Hs epsS SigmaX M betas phit phis
        nsTot Cx Cdelta CH Cd Ceps sDelta Bphi := by
      intro ω hω
      simp only [Set.mem_iInter] at hω
      exact ⟨hω 0, hω 1, hω 2, hω 3, hω 4, hω 5, hω 6, hω 7, hω 8, hω 9⟩
    have hmAbsLe : ∀ (u : Ω → ℝ) (C : ℝ), Measurable u →
        MeasurableSet {ω : Ω | |u ω| ≤ C} := by
      intro u C hu
      have h1 : MeasurableSet {ω : Ω | u ω ≤ C} := hu measurableSet_Iic
      have h2 : MeasurableSet {ω : Ω | -C ≤ u ω} := hu measurableSet_Ici
      have heq : {ω : Ω | |u ω| ≤ C} = {ω : Ω | u ω ≤ C} ∩ {ω : Ω | -C ≤ u ω} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
        exact and_comm
      rw [heq]
      exact h1.inter h2
    have hmAbsLe2 : ∀ (ι κ : Type) [Countable ι] [Countable κ] (u : ι → κ → Ω → ℝ) (C : ℝ),
        (∀ (i : ι) (j : κ), Measurable (u i j)) →
        MeasurableSet {ω : Ω | ∀ (i : ι) (j : κ), |u i j ω| ≤ C} := by
      intro ι κ _ _ u C hu
      have hEq : {ω : Ω | ∀ (i : ι) (j : κ), |u i j ω| ≤ C}
          = ⋂ i : ι, ⋂ j : κ, {ω : Ω | |u i j ω| ≤ C} := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rw [hEq]
      exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => hmAbsLe _ _ (hu i j)))
    have hS1u : ∀ (i j : Fin p), Measurable (fun ω : Ω =>
        (∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * (f (Ht r ω) j + Et r ω j))
          / (nt : ℝ) - SigmaX i j) :=
      fun i j => ((Finset.measurable_sum Finset.univ (fun r _ => hXtprod r i j)).div
        measurable_const).sub measurable_const
    have hS1 : MeasurableSet S1 :=
      hmAbsLe2 (Fin p) (Fin p) (fun i j ω =>
        (∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * (f (Ht r ω) j + Et r ω j))
          / (nt : ℝ) - SigmaX i j) (Cx * aTcoef p nt) hS1u
    have hmAbsLe1 : ∀ (ι : Type) [Countable ι] (u : ι → Ω → ℝ) (C : ℝ),
        (∀ (i : ι), Measurable (u i)) →
        MeasurableSet {ω : Ω | ∀ (i : ι), |u i ω| ≤ C} := by
      intro ι _ u C hu
      have hEq : {ω : Ω | ∀ (i : ι), |u i ω| ≤ C}
          = ⋂ i : ι, {ω : Ω | |u i ω| ≤ C} := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rw [hEq]
      exact MeasurableSet.iInter (fun i => hmAbsLe _ _ (hu i))
    have hS2u : ∀ (i j : Fin p), Measurable (fun ω : Ω =>
        (∑ k : Fin K, ∑ r : Fin (ns k),
          (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j))
          / nsTot - SigmaX i j) :=
      fun i j => ((Finset.measurable_sum Finset.univ (fun k _ =>
        Finset.measurable_sum Finset.univ (fun r _ => hXsprod k r i j))).div
          measurable_const).sub measurable_const
    have hS2 : MeasurableSet S2 :=
      hmAbsLe2 (Fin p) (Fin p) (fun i j ω =>
        (∑ k : Fin K, ∑ r : Fin (ns k),
          (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j)) / nsTot - SigmaX i j)
        (Cx * aSCoef p nsTot) hS2u
    have hS3u : ∀ (i : Fin p), Measurable (fun ω : Ω =>
        (∑ k : Fin K, (ns k : ℝ) * ∑ j : Fin p,
          ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j))
            / (ns k : ℝ) - SigmaX i j) * (betas k j - betaBar ns nsTot betas j)) / nsTot) := by
      intro i
      refine (Finset.measurable_sum Finset.univ (fun k _ => ?_)).div measurable_const
      refine measurable_const.mul ?_
      refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
      refine Measurable.mul ?_ measurable_const
      exact ((Finset.measurable_sum Finset.univ (fun r _ => hXsprod k r i j)).div
        measurable_const).sub measurable_const
    have hS3 : MeasurableSet S3 :=
      hmAbsLe1 (Fin p) (fun i ω =>
        (∑ k : Fin K, (ns k : ℝ) * ∑ j : Fin p,
          ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j))
            / (ns k : ℝ) - SigmaX i j) * (betas k j - betaBar ns nsTot betas j)) / nsTot)
        (Cdelta * sDelta * aSCoef p nsTot) hS3u
    have hS8u : ∀ (i : Fin p), Measurable (fun ω : Ω =>
        (∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * epsT r ω) / (nt : ℝ)) :=
      fun i => (Finset.measurable_sum Finset.univ (fun r _ => hXtEps r i)).div measurable_const
    have hS8 : MeasurableSet S8 :=
      hmAbsLe1 (Fin p) (fun i ω =>
        (∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * epsT r ω) / (nt : ℝ))
        (Ceps * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ))) hS8u
    have hS9u : ∀ (i : Fin p), Measurable (fun ω : Ω =>
        (∑ k : Fin K, ∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * epsS k r ω) / nsTot) :=
      fun i => (Finset.measurable_sum Finset.univ (fun k _ =>
        Finset.measurable_sum Finset.univ (fun r _ => hXsEps k r i))).div measurable_const
    have hS9 : MeasurableSet S9 :=
      hmAbsLe1 (Fin p) (fun i ω =>
        (∑ k : Fin K, ∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * epsS k r ω) / nsTot)
        (Ceps * Real.sqrt (Real.log (p : ℝ) / nsTot)) hS9u
    have hS10u : ∀ (i : Fin p), Measurable (fun ω : Ω =>
        (∑ k : Fin K, ∑ j : Fin q,
          ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * Hs k r ω j) - (ns k : ℝ) * M i j)
            * (phis k j - phit j)) / nsTot) := by
      intro i
      refine (Finset.measurable_sum Finset.univ (fun k _ => ?_)).div measurable_const
      refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
      refine Measurable.mul ?_ measurable_const
      exact (Finset.measurable_sum Finset.univ (fun r _ =>
        (hXscoord k r i).mul (hHscoord k r j))).sub
        (measurable_const : Measurable fun _ : Ω => (ns k : ℝ) * M i j)
    have hS10 : MeasurableSet S10 :=
      hmAbsLe1 (Fin p) (fun i ω =>
        (∑ k : Fin K, ∑ j : Fin q,
          ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * Hs k r ω j) - (ns k : ℝ) * M i j)
            * (phis k j - phit j)) / nsTot)
        (Cd * Bphi * Real.sqrt (q : ℝ) * aSCoef p nsTot) hS10u
    have hmSqrtLe : ∀ (C : ℝ), 0 ≤ C → ∀ (u : Fin p → Fin q → Ω → ℝ),
        (∀ (i : Fin p) (j : Fin q), Measurable (u i j)) →
        MeasurableSet {ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, (u i j ω) ^ 2) ≤ C} := by
      intro C hC u hu
      have hEq : {ω : Ω | ∀ (i : Fin p), Real.sqrt (∑ j : Fin q, (u i j ω) ^ 2) ≤ C}
          = ⋂ i : Fin p, {ω : Ω | Real.sqrt (∑ j : Fin q, (u i j ω) ^ 2) ≤ C} := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rw [hEq]
      refine MeasurableSet.iInter (fun i => ?_)
      have hmeas : Measurable (fun ω : Ω => Real.sqrt (∑ j : Fin q, (u i j ω) ^ 2)) := by
        refine Real.continuous_sqrt.measurable.comp ?_
        have hsq : ∀ j : Fin q, Measurable (fun ω : Ω => (u i j ω) ^ 2) := by
          intro j
          simpa only [pow_two] using (hu i j).mul (hu i j)
        exact Finset.measurable_sum Finset.univ (fun j _ => hsq j)
      exact hmeas measurableSet_Iic
    have hS4 : MeasurableSet S4 :=
      hmSqrtLe (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (nt : ℝ)))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun i j ω => (∑ r : Fin nt, f (Ht r ω) i * Ht r ω j) / (nt : ℝ) - M i j)
        (fun i j => ((Finset.measurable_sum Finset.univ (fun r _ => hXtprodH r i j)).div
          measurable_const).sub measurable_const)
    have hS5 : MeasurableSet S5 :=
      hmSqrtLe (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun i j ω => (∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i * Hs k r ω j) / nsTot - M i j)
        (fun i j => ((Finset.measurable_sum Finset.univ (fun k _ =>
          Finset.measurable_sum Finset.univ (fun r _ => hXsprodH k r i j))).div
            measurable_const).sub measurable_const)
    have hS6 : MeasurableSet S6 :=
      hmSqrtLe (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (nt : ℝ)))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun i j ω => (∑ r : Fin nt, Et r ω i * Ht r ω j) / (nt : ℝ))
        (fun i j => (Finset.measurable_sum Finset.univ (fun r _ => hEtprodH r i j)).div
          measurable_const)
    have hS7 : MeasurableSet S7 :=
      hmSqrtLe (CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun i j ω => (∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i * Hs k r ω j) / nsTot)
        (fun i j => (Finset.measurable_sum Finset.univ (fun k _ =>
          Finset.measurable_sum Finset.univ (fun r _ => hEsprodH k r i j))).div
            measurable_const)
    have hindT : iIndepFun (fun (i : Fin nt) ω => ((Et i ω, Ht i ω), epsT i ω)) mu :=
      (statopia_math_node_2082055502_c6d14abe mu (pooledRow Et Ht epsT Es Hs epsS) hInd
        (fun (r : Fin nt) => Sum.inl r) (fun a b h => Sum.inl_injective h)).1
    have hindS : iIndepFun (fun (x : (k : Fin K) × Fin (ns k)) ω =>
        ((Es x.1 x.2 ω, Hs x.1 x.2 ω), epsS x.1 x.2 ω)) mu :=
      (statopia_math_node_2082055502_c6d14abe mu (pooledRow Et Ht epsT Es Hs epsS) hInd
        (fun x : (k : Fin K) × Fin (ns k) => Sum.inr x) (fun a b h => Sum.inr_injective h)).1
    have hS8good : 1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S8 := by
      haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
      have h8 := _h5 p hp nt hnt hNeps_le f (Real.sqrt sigmaSq) (Real.sqrt_nonneg sigmaSq)
        hf Ω mu
        (fun ω (i : Fin nt) => Et i ω) (fun ω (i : Fin nt) => Ht i ω)
        (fun ω (i : Fin nt) => epsT i ω)
        hindT hidentT (fun i j => hEcoord i j) (fun i k => hHcoord i k) hepsTm
        (fun i j => hIntE_mu i j) (fun i k => hIntH_mu i k) (fun i j => hIntfH_mu i j)
        hIntEpsT hIntEpsT2 (fun i j k => hIntEH_mu i j k) (fun i j => hE0_mu i j)
        (fun i k => hH0_mu i k) (fun i j => hfH0_mu i j) (fun i j => hSgE_mu i j)
        (fun i k => hSgH_mu i k) (fun i j => hSgfH_mu i j) (fun i j k => hEH0_mu i j k)
        hEpsT0 (fun i => by rw [Real.sq_sqrt hsigmaSq]; exact hEpsT2 i) hSgEpsT hIndepT
      refine le_trans h8 ?_
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hω' : ‖(fun j : Fin p => 1 / (nt : ℝ) * ∑ r : Fin nt,
          (f (Ht r ω) j + Et r ω j) * epsT r ω)‖
          ≤ Ceps * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ)) := hω
      have hnorm : ‖(fun j : Fin p => 1 / (nt : ℝ) * ∑ r : Fin nt,
            (f (Ht r ω) j + Et r ω j) * epsT r ω)‖
          = Finset.univ.sup' Finset.univ_nonempty (fun j : Fin p => |1 / (nt : ℝ) *
              ∑ r : Fin nt, (f (Ht r ω) j + Et r ω j) * epsT r ω|) :=
        Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs _
      intro i
      have h1 : |(1 / (nt : ℝ)) * ∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * epsT r ω|
          ≤ Ceps * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ)) := by
        have hle : |1 / (nt : ℝ) * ∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * epsT r ω|
            ≤ ‖(fun j : Fin p => 1 / (nt : ℝ) * ∑ r : Fin nt,
              (f (Ht r ω) j + Et r ω j) * epsT r ω)‖ := by
          rw [hnorm]
          exact Finset.le_sup' (s := Finset.univ) (f := fun j : Fin p => |1 / (nt : ℝ) *
            ∑ r : Fin nt, (f (Ht r ω) j + Et r ω j) * epsT r ω|) (Finset.mem_univ i)
        exact le_trans hle hω'
      have h3 : (1 / (nt : ℝ)) * ∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * epsT r ω
          = (∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * epsT r ω) / (nt : ℝ) := by
        ring
      rwa [h3] at h1
    have hS8cmp : mu.real S8ᶜ ≤ (p : ℝ).rpow (-c) / 20 := hcompl S8 hS8 hS8good
    have hindTpair : iIndepFun (fun i : Fin nt => fun ω => (Et i ω, Ht i ω)) mu :=
      hindT.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
    have hindSpair : iIndepFun (fun x : (k : Fin K) × Fin (ns k) =>
        fun ω => (Es x.1 x.2 ω, Hs x.1 x.2 ω)) mu :=
      hindS.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
    have hIntXH_muS : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p) (j : Fin q),
        Integrable (fun ω => (f (Hs k r ω) i + Es k r ω i) * Hs k r ω j) mu := by
      intro k r i j
      exact (MeasureTheory.integrable_map_measure
        (μ := mu) (f := fun ω => (Es k r ω, Hs k r ω))
        (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) => (f x.2 i + x.1 i) * x.2 j)
        (by rw [hmapS k r]; exact (hIntXH i j).1)
        (hpairSm k r).aemeasurable).mp (by rw [hmapS k r]; exact hIntXH i j)
    have hM_muS : ∀ (k : Fin K) (r : Fin (ns k)) (i : Fin p) (j : Fin q),
        M i j = ∫ ω, (f (Hs k r ω) i + Es k r ω i) * Hs k r ω j ∂mu := by
      intro k r i j
      have h := MeasureTheory.integral_map (μ := mu) (φ := fun ω => (Es k r ω, Hs k r ω))
        (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) => (f x.2 i + x.1 i) * x.2 j)
        (hpairSm k r).aemeasurable
        (by rw [hmapS k r]; exact (hIntXH i j).1)
      rw [hmapS k r] at h
      simpa using (hM i j).trans h
    have hps : ((PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.pooledSourceSize ns : ℕ) : ℝ)
        = nsTot := hpool'
    have hNd_pool : Nd * Real.log (p : ℝ) ≤
        ((PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.pooledSourceSize ns : ℕ) : ℝ) := by
      rw [hps]
      exact hNd_leS
    have hS10good : 1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S10 := by
      haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
      have hd : ∀ k : Fin K,
          ‖(WithLp.toLp 2 (phis k - phit) : EuclideanSpace ℝ (Fin q))‖ ≤ Bphi := by
        intro k
        have h1 : ‖(WithLp.toLp 2 (phis k - phit) : EuclideanSpace ℝ (Fin q))‖
            = l2norm (phis k - phit) := by
          rw [EuclideanSpace.norm_eq, l2norm]
          simp only [Real.norm_eq_abs, sq_abs]
        rw [h1]
        exact hphik k
      have h4' := _h4 p q K hp hq hK nt ns hnt hns hnt_le_pool Bphi hBphi (μ := mu)
      have h10 := h4' f Es Hs M (fun k => WithLp.toLp 2 (phis k - phit))
        hf (fun k i => hEsm k i) (fun k i => hHsm k i)
        (fun k i j => hSgEs_mu k i j) (fun k i l => hSgHs_mu k i l) (fun k i j => hSgfHs_mu k i j)
        (fun k i j => hIntEs_mu k i j) (fun k i l => hIntHs_mu k i l) (fun k i j => hIntfHs_mu k i j)
        (fun k i j l => hIntEH_muS k i j l) (fun k i j l => hIntXH_muS k i j l)
        (fun k i j => hEs0_mu k i j) (fun k i l => hHs0_mu k i l) (fun k i j => hfHs0_mu k i j)
        (fun k i j l => hEH0_muS k i j l) (fun k i j l => hM_muS k i j l)
        hindSpair hidentS hd hNd_pool
      refine le_trans h10 ?_
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hconst : Real.sqrt (Real.log (p : ℝ) /
            ((PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.pooledSourceSize ns : ℕ) : ℝ))
          = aSCoef p nsTot := by
        rw [haS_eq, hps, hpool']
      have hcoord : ∀ i : Fin p,
          (PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.weightedTransferVec
              ns f Es Hs M (fun k => WithLp.toLp 2 (phis k - phit)) ω) i
            = (∑ k : Fin K, ∑ j : Fin q,
                ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * Hs k r ω j) - (ns k : ℝ) * M i j)
                  * (phis k j - phit j)) / nsTot := by
        intro i
        rw [PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.weightedTransferVec]
        simp only [hps, Pi.sub_apply]
        ring
      intro i
      have h1 : |(PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.weightedTransferVec
            ns f Es Hs M (fun k => WithLp.toLp 2 (phis k - phit)) ω) i|
          ≤ Cd * Bphi * Real.sqrt (q : ℝ) *
            Real.sqrt (Real.log (p : ℝ) /
              ((PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.pooledSourceSize ns : ℕ) : ℝ)) := by
        have hnorm := Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs
          (PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.weightedTransferVec
            ns f Es Hs M (fun k => WithLp.toLp 2 (phis k - phit)) ω)
        have hle := Finset.le_sup'
          (f := fun j : Fin p => |(PaperProofTasks.job_paper_110bb96e917848c19df0625891303d5c.Statlib.Imported.weightedTransferVec
            ns f Es Hs M (fun k => WithLp.toLp 2 (phis k - phit)) ω) j|)
          (Finset.mem_univ i)
        rw [← hnorm] at hle
        exact le_trans hle hω
      rw [hcoord i, hconst] at h1
      exact h1
    have hS10cmp : mu.real S10ᶜ ≤ (p : ℝ).rpow (-c) / 20 := hcompl S10 hS10 hS10good
    have hSall : ∀ j : Fin 10, MeasurableSet (S j) := by
      intro j
      fin_cases j
      · exact hS1
      · exact hS2
      · exact hS3
      · exact hS4
      · exact hS5
      · exact hS6
      · exact hS7
      · exact hS8
      · exact hS9
      · exact hS10
    have hS9good : 1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S9 := by
      haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
      have hcard : Fintype.card ((k : Fin K) × Fin (ns k)) = ∑ k : Fin K, ns k := by
        rw [Fintype.card_sigma]
        simp
      have eS : ((k : Fin K) × Fin (ns k)) ≃ Fin (∑ k : Fin K, ns k) :=
        Fintype.equivFinOfCardEq hcard
      have hind9 : iIndepFun (fun (i : Fin (∑ k : Fin K, ns k)) ω =>
          ((Es (eS.symm i).1 (eS.symm i).2 ω, Hs (eS.symm i).1 (eS.symm i).2 ω),
            epsS (eS.symm i).1 (eS.symm i).2 ω)) mu :=
        (statopia_math_node_2082055502_c6d14abe mu
          (fun (x : (k : Fin K) × Fin (ns k)) ω =>
            ((Es x.1 x.2 ω, Hs x.1 x.2 ω), epsS x.1 x.2 ω)) hindS
          eS.symm eS.symm.injective).1
      have hNeps_pool : Neps * Real.log (p : ℝ) ≤ ((∑ k : Fin K, ns k : ℕ) : ℝ) := by
        rw [hpool']
        exact hNeps_leS
      have h9 := _h5 p hp (∑ k : Fin K, ns k) hpoolN_pos hNeps_pool f (Real.sqrt sigmaSq)
        (Real.sqrt_nonneg sigmaSq) hf Ω mu
        (fun ω (i : Fin (∑ k : Fin K, ns k)) j => Es (eS.symm i).1 (eS.symm i).2 ω j)
        (fun ω (i : Fin (∑ k : Fin K, ns k)) j => Hs (eS.symm i).1 (eS.symm i).2 ω j)
        (fun ω (i : Fin (∑ k : Fin K, ns k)) => epsS (eS.symm i).1 (eS.symm i).2 ω)
        hind9 (fun i j => hidentS (eS.symm i) (eS.symm j))
        (fun i j => hEscoord (eS.symm i).1 (eS.symm i).2 j)
        (fun i l => hHscoord (eS.symm i).1 (eS.symm i).2 l)
        (fun i => hepsSm (eS.symm i).1 (eS.symm i).2)
        (fun i j => hIntEs_mu (eS.symm i).1 (eS.symm i).2 j)
        (fun i l => hIntHs_mu (eS.symm i).1 (eS.symm i).2 l)
        (fun i j => hIntfHs_mu (eS.symm i).1 (eS.symm i).2 j)
        (fun i => hIntEpsS (eS.symm i).1 (eS.symm i).2)
        (fun i => hIntEpsS2 (eS.symm i).1 (eS.symm i).2)
        (fun i j l => hIntEH_muS (eS.symm i).1 (eS.symm i).2 j l)
        (fun i j => hEs0_mu (eS.symm i).1 (eS.symm i).2 j)
        (fun i l => hHs0_mu (eS.symm i).1 (eS.symm i).2 l)
        (fun i j => hfHs0_mu (eS.symm i).1 (eS.symm i).2 j)
        (fun i j => hSgEs_mu (eS.symm i).1 (eS.symm i).2 j)
        (fun i l => hSgHs_mu (eS.symm i).1 (eS.symm i).2 l)
        (fun i j => hSgfHs_mu (eS.symm i).1 (eS.symm i).2 j)
        (fun i j l => hEH0_muS (eS.symm i).1 (eS.symm i).2 j l)
        (fun i => hEpsS0 (eS.symm i).1 (eS.symm i).2)
        (fun i => by rw [Real.sq_sqrt hsigmaSq]; exact hEpsS2 (eS.symm i).1 (eS.symm i).2)
        (fun i => hSgEpsS (eS.symm i).1 (eS.symm i).2)
        (fun i => hIndepS (eS.symm i).1 (eS.symm i).2)
      have hsum9 : ∀ (G : (k : Fin K) → Fin (ns k) → ℝ),
          (∑ i : Fin (∑ k : Fin K, ns k), G (eS.symm i).1 (eS.symm i).2) = ∑ k : Fin K, ∑ r, G k r := by
        intro G
        rw [← Fintype.sum_sigma' G]
        exact Equiv.sum_comp eS.symm (fun x => G x.1 x.2)
      refine le_trans h9 ?_
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hω' : ‖(fun j : Fin p => 1 / ((∑ k : Fin K, ns k : ℕ) : ℝ) *
            ∑ i : Fin (∑ k : Fin K, ns k),
              (f (Hs (eS.symm i).1 (eS.symm i).2 ω) j + Es (eS.symm i).1 (eS.symm i).2 ω j) *
                epsS (eS.symm i).1 (eS.symm i).2 ω)‖
          ≤ Ceps * Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ)) := by
        simpa using hω
      have hnorm : ‖(fun j : Fin p => 1 / ((∑ k : Fin K, ns k : ℕ) : ℝ) *
            ∑ i : Fin (∑ k : Fin K, ns k),
              (f (Hs (eS.symm i).1 (eS.symm i).2 ω) j + Es (eS.symm i).1 (eS.symm i).2 ω j) *
                epsS (eS.symm i).1 (eS.symm i).2 ω)‖
          = Finset.univ.sup' Finset.univ_nonempty (fun j : Fin p =>
              |1 / ((∑ k : Fin K, ns k : ℕ) : ℝ) *
                ∑ i : Fin (∑ k : Fin K, ns k),
                  (f (Hs (eS.symm i).1 (eS.symm i).2 ω) j + Es (eS.symm i).1 (eS.symm i).2 ω j) *
                    epsS (eS.symm i).1 (eS.symm i).2 ω|) :=
        Statlib.HighDim.CovarianceMatrix.pi_real_norm_eq_sup_abs _
      intro i
      have h1 : |(1 / ((∑ k : Fin K, ns k : ℕ) : ℝ)) *
            ∑ i' : Fin (∑ k : Fin K, ns k),
              (f (Hs (eS.symm i').1 (eS.symm i').2 ω) i + Es (eS.symm i').1 (eS.symm i').2 ω i) *
                epsS (eS.symm i').1 (eS.symm i').2 ω|
          ≤ Ceps * Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ)) := by
        have hle : |(1 / ((∑ k : Fin K, ns k : ℕ) : ℝ)) *
              ∑ i' : Fin (∑ k : Fin K, ns k),
                (f (Hs (eS.symm i').1 (eS.symm i').2 ω) i + Es (eS.symm i').1 (eS.symm i').2 ω i) *
                  epsS (eS.symm i').1 (eS.symm i').2 ω|
            ≤ ‖(fun j : Fin p => 1 / ((∑ k : Fin K, ns k : ℕ) : ℝ) *
                ∑ i' : Fin (∑ k : Fin K, ns k),
                  (f (Hs (eS.symm i').1 (eS.symm i').2 ω) j + Es (eS.symm i').1 (eS.symm i').2 ω j) *
                    epsS (eS.symm i').1 (eS.symm i').2 ω)‖ := by
          rw [hnorm]
          exact Finset.le_sup' (s := Finset.univ) (f := fun j : Fin p =>
            |1 / ((∑ k : Fin K, ns k : ℕ) : ℝ) *
              ∑ i' : Fin (∑ k : Fin K, ns k),
                (f (Hs (eS.symm i').1 (eS.symm i').2 ω) j + Es (eS.symm i').1 (eS.symm i').2 ω j) *
                  epsS (eS.symm i').1 (eS.symm i').2 ω|) (Finset.mem_univ i)
        exact le_trans hle hω'
      have hsumi := hsum9 (fun (k : Fin K) (r : Fin (ns k)) =>
        (f (Hs k r ω) i + Es k r ω i) * epsS k r ω)
      simp only [] at hsumi
      rw [hsumi] at h1
      have h3 : (1 / ((∑ k : Fin K, ns k : ℕ) : ℝ)) *
            ∑ k : Fin K, ∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * epsS k r ω
          = (∑ k : Fin K, ∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) * epsS k r ω) / nsTot := by
        rw [hpool']
        ring
      rw [h3] at h1
      have h4 : Ceps * Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ))
          = Ceps * Real.sqrt (Real.log (p : ℝ) / nsTot) := by rw [hpool']
      rw [h4] at h1
      exact h1
    have hS9cmp : mu.real S9ᶜ ≤ (p : ℝ).rpow (-c) / 20 := hcompl S9 hS9 hS9good
    have hS1good : (1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S1) ∧
        (1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S2) := by
      let P : Measure ((Fin q → ℝ) × (Fin p → ℝ)) := Measure.map Prod.swap Prow
      haveI hPprob : IsProbabilityMeasure P :=
        MeasureTheory.Measure.isProbabilityMeasure_map (μ := Prow) (f := Prod.swap)
          measurable_swap.aemeasurable
      have hstep : Measure.map Prod.swap (Measure.map Prod.swap Prow)
          = Measure.map (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Prod.swap (Prod.swap x)) Prow := by
        rw [MeasureTheory.Measure.map_map measurable_swap measurable_swap]
        rfl
      have hmm : Measure.map Prod.swap (Measure.map Prod.swap Prow) = Prow := by
        rw [hstep]
        have hid : (fun x : (Fin p → ℝ) × (Fin q → ℝ) => Prod.swap (Prod.swap x)) = id := by
          funext x
          cases x with
          | mk a b => rfl
        rw [hid, MeasureTheory.Measure.map_id]
      have hmeasQP : ∀ (i j : Fin p), Measurable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) := by
        intro i j
        exact (((measurable_pi_apply i).comp (hf.comp measurable_fst)).add
          ((measurable_pi_apply i).comp measurable_snd)).mul
          (((measurable_pi_apply j).comp (hf.comp measurable_fst)).add
            ((measurable_pi_apply j).comp measurable_snd))
      have hSgPE : ∀ i : Fin p,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i)
            (Real.toNNReal ((Real.sqrt L) ^ 2)) P := by
        intro i
        refine ProbabilityTheory.HasSubgaussianMGF.of_map (μ := Measure.map Prod.swap Prow)
          (Y := Prod.swap) (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 i)
          measurable_swap.aemeasurable ?_
        rw [hparamNN, hmm]
        simpa using hSgE i
      have hSgPH : ∀ j : Fin q,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j)
            (Real.toNNReal ((Real.sqrt L) ^ 2)) P := by
        intro j
        refine ProbabilityTheory.HasSubgaussianMGF.of_map (μ := Measure.map Prod.swap Prow)
          (Y := Prod.swap) (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.2 j)
          measurable_swap.aemeasurable ?_
        rw [hparamNN, hmm]
        simpa using hSgH j
      have hSgPfH : ∀ k : Fin p,
          HasSubgaussianMGF (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k)
            (Real.toNNReal ((Real.sqrt L) ^ 2)) P := by
        intro k
        refine ProbabilityTheory.HasSubgaussianMGF.of_map (μ := Measure.map Prod.swap Prow)
          (Y := Prod.swap) (X := fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 k)
          measurable_swap.aemeasurable ?_
        rw [hparamNN, hmm]
        simpa using hSgf k
      have hIntPE : ∀ i : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i) P := by
        intro i
        exact (MeasureTheory.integrable_map_measure
          (μ := Prow) (f := Prod.swap)
          (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i)
          ((measurable_pi_apply i).comp measurable_snd).aestronglyMeasurable
          measurable_swap.aemeasurable).mpr (by simpa using hIntE i)
      have hIntPH : ∀ j : Fin q, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j) P := by
        intro j
        exact (MeasureTheory.integrable_map_measure
          (μ := Prow) (f := Prod.swap)
          (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j)
          ((measurable_pi_apply j).comp measurable_fst).aestronglyMeasurable
          measurable_swap.aemeasurable).mpr (by simpa using hIntH j)
      have hIntPfH : ∀ k : Fin p, Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k) P := by
        intro k
        exact (MeasureTheory.integrable_map_measure
          (μ := Prow) (f := Prod.swap)
          (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k)
          ((measurable_pi_apply k).comp (hf.comp measurable_fst)).aestronglyMeasurable
          measurable_swap.aemeasurable).mpr (by simpa using hIntf k)
      have hE0P : ∀ i : Fin p, ∫ z : (Fin q → ℝ) × (Fin p → ℝ), z.2 i ∂P = 0 := by
        intro i
        have h := MeasureTheory.integral_map (μ := Prow) (φ := Prod.swap)
          (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i)
          measurable_swap.aemeasurable
          ((measurable_pi_apply i).comp measurable_snd).aestronglyMeasurable
        exact h.trans (by simpa using hE0 i)
      have hH0P : ∀ j : Fin q, ∫ z : (Fin q → ℝ) × (Fin p → ℝ), z.1 j ∂P = 0 := by
        intro j
        have h := MeasureTheory.integral_map (μ := Prow) (φ := Prod.swap)
          (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.1 j)
          measurable_swap.aemeasurable
          ((measurable_pi_apply j).comp measurable_fst).aestronglyMeasurable
        exact h.trans (by simpa using hH0 j)
      have hfH0P : ∀ k : Fin p, ∫ z : (Fin q → ℝ) × (Fin p → ℝ), f z.1 k ∂P = 0 := by
        intro k
        have h := MeasureTheory.integral_map (μ := Prow) (φ := Prod.swap)
          (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 k)
          measurable_swap.aemeasurable
          ((measurable_pi_apply k).comp (hf.comp measurable_fst)).aestronglyMeasurable
        exact h.trans (by simpa using hf0 k)
      have hIntPEH : ∀ (i : Fin p) (j : Fin q),
          Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i * z.1 j) P := by
        intro i j
        exact (MeasureTheory.integrable_map_measure
          (μ := Prow) (f := Prod.swap)
          (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i * z.1 j)
          (((measurable_pi_apply i).comp measurable_snd).mul
            ((measurable_pi_apply j).comp measurable_fst)).aestronglyMeasurable
          measurable_swap.aemeasurable).mpr (by simpa using hIntEH i j)
      have hEH0P : ∀ (i : Fin p) (j : Fin q),
          ∫ z : (Fin q → ℝ) × (Fin p → ℝ), z.2 i * z.1 j ∂P = 0 := by
        intro i j
        have h := MeasureTheory.integral_map (μ := Prow) (φ := Prod.swap)
          (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) => z.2 i * z.1 j)
          measurable_swap.aemeasurable
          (((measurable_pi_apply i).comp measurable_snd).mul
            ((measurable_pi_apply j).comp measurable_fst)).aestronglyMeasurable
        exact h.trans (by simpa using hEH0 i j)
      have hIntPX : ∀ (i j : Fin p), Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
          (f z.1 i + z.2 i) * (f z.1 j + z.2 j)) P := by
        intro i j
        exact (MeasureTheory.integrable_map_measure
          (μ := Prow) (f := Prod.swap)
          (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
            (f z.1 i + z.2 i) * (f z.1 j + z.2 j))
          (hmeasQP i j).aestronglyMeasurable
          measurable_swap.aemeasurable).mpr (by simpa using hIntX i j)
      have hrowsMeas : ∀ l : Fin nt, Measurable (fun ω => (Ht l ω, Et l ω)) :=
        fun l => (hHtm l).prod (hEtm l)
      have hrowsInd : iIndepFun (fun l : Fin nt => fun ω => (Ht l ω, Et l ω)) mu :=
        hindTpair.comp (fun _ => Prod.swap) (fun _ => measurable_swap)
      have hrowsMap : ∀ l : Fin nt, Measure.map (fun ω => (Ht l ω, Et l ω)) mu = P := by
        intro l
        have h := MeasureTheory.Measure.map_map (μ := mu)
          (f := fun ω => (Et l ω, Ht l ω)) (g := Prod.swap) measurable_swap (hpairTm l)
        rw [hmapT l] at h
        exact h.symm
      have hres := _h1 p hp f hf P hPprob hIntPE hIntPH hIntPfH hE0P hH0P hfH0P
        hSgPE hSgPH hSgPfH hIntPEH hEH0P hIntPX nt hnt hNx_le Ω mu (by infer_instance)
        (fun l ω => (Ht l ω, Et l ω)) hrowsMeas hrowsInd hrowsMap
      have hS2part : 1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S2 := by
        have hcard2 : Fintype.card ((k : Fin K) × Fin (ns k)) = ∑ k : Fin K, ns k := by
          rw [Fintype.card_sigma]
          simp
        have eS2 : ((k : Fin K) × Fin (ns k)) ≃ Fin (∑ k : Fin K, ns k) :=
          Fintype.equivFinOfCardEq hcard2
        have hrowsMeas2 : ∀ l : Fin (∑ k : Fin K, ns k),
            Measurable (fun ω => (Hs (eS2.symm l).1 (eS2.symm l).2 ω,
              Es (eS2.symm l).1 (eS2.symm l).2 ω)) :=
          fun l => (hHsm (eS2.symm l).1 (eS2.symm l).2).prod
            (hEsm (eS2.symm l).1 (eS2.symm l).2)
        have hrowsInd2 : iIndepFun (fun (l : Fin (∑ k : Fin K, ns k)) ω =>
            (Hs (eS2.symm l).1 (eS2.symm l).2 ω, Es (eS2.symm l).1 (eS2.symm l).2 ω)) mu :=
          ((statopia_math_node_2082055502_c6d14abe mu
            (fun (x : (k : Fin K) × Fin (ns k)) ω =>
              (Es x.1 x.2 ω, Hs x.1 x.2 ω)) hindSpair
            eS2.symm eS2.symm.injective).1).comp (fun _ => Prod.swap)
            (fun _ => measurable_swap)
        have hrowsMap2 : ∀ l : Fin (∑ k : Fin K, ns k),
            Measure.map (fun ω => (Hs (eS2.symm l).1 (eS2.symm l).2 ω,
              Es (eS2.symm l).1 (eS2.symm l).2 ω)) mu = P := by
          intro l
          have h := MeasureTheory.Measure.map_map (μ := mu)
            (f := fun ω => (Es (eS2.symm l).1 (eS2.symm l).2 ω,
              Hs (eS2.symm l).1 (eS2.symm l).2 ω))
            (g := Prod.swap) measurable_swap (hpairSm (eS2.symm l).1 (eS2.symm l).2)
          rw [hmapS (eS2.symm l).1 (eS2.symm l).2] at h
          exact h.symm
        have hres2 := _h1 p hp f hf P hPprob hIntPE hIntPH hIntPfH hE0P hH0P hfH0P
          hSgPE hSgPH hSgPfH hIntPEH hEH0P hIntPX (∑ k : Fin K, ns k) hpoolN_pos
          (by rw [hpool']; exact hNx_leS) Ω mu (by infer_instance)
          (fun (l : Fin (∑ k : Fin K, ns k)) ω =>
            (Hs (eS2.symm l).1 (eS2.symm l).2 ω, Es (eS2.symm l).1 (eS2.symm l).2 ω))
          hrowsMeas2 hrowsInd2 hrowsMap2
        have hsum9s : ∀ (G : (k : Fin K) → Fin (ns k) → ℝ),
            (∑ l : Fin (∑ k : Fin K, ns k), G (eS2.symm l).1 (eS2.symm l).2)
              = ∑ k : Fin K, ∑ r, G k r := by
          intro G
          rw [← Fintype.sum_sigma' G]
          exact Equiv.sum_comp eS2.symm (fun x => G x.1 x.2)
        refine le_trans hres2 ?_
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro i j
        have h1 := hω i j
        have hsum : (∑ x : Fin (∑ k : Fin K, ns k),
              (f (Hs (eS2.symm x).1 (eS2.symm x).2 ω) i *
                  f (Hs (eS2.symm x).1 (eS2.symm x).2 ω) j
                + f (Hs (eS2.symm x).1 (eS2.symm x).2 ω) i *
                    Es (eS2.symm x).1 (eS2.symm x).2 ω j
                + Es (eS2.symm x).1 (eS2.symm x).2 ω i *
                    f (Hs (eS2.symm x).1 (eS2.symm x).2 ω) j
                + Es (eS2.symm x).1 (eS2.symm x).2 ω i *
                    Es (eS2.symm x).1 (eS2.symm x).2 ω j))
            = ∑ x : Fin (∑ k : Fin K, ns k),
              (f (Hs (eS2.symm x).1 (eS2.symm x).2 ω) i +
                  Es (eS2.symm x).1 (eS2.symm x).2 ω i) *
                (f (Hs (eS2.symm x).1 (eS2.symm x).2 ω) j +
                  Es (eS2.symm x).1 (eS2.symm x).2 ω j) :=
          Finset.sum_congr rfl (fun x _ => by ring)
        have hemp2 : PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.empSigma
              f (fun (l : Fin (∑ k : Fin K, ns k)) ω =>
                (Hs (eS2.symm l).1 (eS2.symm l).2 ω, Es (eS2.symm l).1 (eS2.symm l).2 ω))
              ω i j
            = (∑ l : Fin (∑ k : Fin K, ns k),
                (f (Hs (eS2.symm l).1 (eS2.symm l).2 ω) i +
                    Es (eS2.symm l).1 (eS2.symm l).2 ω i) *
                  (f (Hs (eS2.symm l).1 (eS2.symm l).2 ω) j +
                    Es (eS2.symm l).1 (eS2.symm l).2 ω j))
              / ((∑ k : Fin K, ns k : ℕ) : ℝ) := by
          simp only [PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.empSigma,
            Matrix.of_apply, hsum, div_eq_inv_mul]
        have hsigi : PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.SigmaX
              f P i j = SigmaX i j := by
          have h := MeasureTheory.integral_map (μ := Prow) (φ := Prod.swap)
            (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
              (f z.1 i + z.2 i) * (f z.1 j + z.2 j))
            measurable_swap.aemeasurable (hmeasQP i j).aestronglyMeasurable
          show (∫ z : (Fin q → ℝ) × (Fin p → ℝ),
              (f z.1 i + z.2 i) * (f z.1 j + z.2 j) ∂(Measure.map Prod.swap Prow))
            = SigmaX i j
          rw [h]
          simpa using (hSigmaX i j).symm
        rw [hemp2, hsigi] at h1
        have hsumi := hsum9s (fun (k : Fin K) (r : Fin (ns k)) =>
          (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j))
        simp only [] at hsumi
        rw [hsumi] at h1
        have h3 : (∑ k : Fin K, ∑ r : Fin (ns k),
              (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j))
              / ((∑ k : Fin K, ns k : ℕ) : ℝ)
            = (∑ k : Fin K, ∑ r : Fin (ns k),
              (f (Hs k r ω) i + Es k r ω i) * (f (Hs k r ω) j + Es k r ω j)) / nsTot := by
          rw [hpool']
        have h4 : Cx * Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ))
            = Cx * aSCoef p nsTot := by
          rw [haS_eq]
        rw [h3, h4] at h1
        exact h1
      refine ⟨?_, hS2part⟩
  
      refine le_trans hres ?_
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro i j
      have h1 := hω i j
      have hemp : PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.empSigma
            f (fun l ω => (Ht l ω, Et l ω)) ω i j
          = (∑ r : Fin nt, (f (Ht r ω) i + Et r ω i) * (f (Ht r ω) j + Et r ω j)) / (nt : ℝ) := by
        have hsum : (∑ x : Fin nt, (f (Ht x ω) i * f (Ht x ω) j + f (Ht x ω) i * Et x ω j
              + Et x ω i * f (Ht x ω) j + Et x ω i * Et x ω j))
            = ∑ x : Fin nt, (f (Ht x ω) i + Et x ω i) * (f (Ht x ω) j + Et x ω j) :=
          Finset.sum_congr rfl (fun x _ => by ring)
        simp only [PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.empSigma,
          Matrix.of_apply, hsum, div_eq_inv_mul]
      have hsig : PaperProofTasks.job_paper_4a6904a098fa4fcebf3058bbb4e15c0e.Statlib.Imported.SigmaX
            f P i j = SigmaX i j := by
        have h := MeasureTheory.integral_map (μ := Prow) (φ := Prod.swap)
          (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) =>
            (f z.1 i + z.2 i) * (f z.1 j + z.2 j))
          measurable_swap.aemeasurable (hmeasQP i j).aestronglyMeasurable
        show (∫ z : (Fin q → ℝ) × (Fin p → ℝ),
            (f z.1 i + z.2 i) * (f z.1 j + z.2 j) ∂(Measure.map Prod.swap Prow)) = SigmaX i j
        rw [h]
        simpa using (hSigmaX i j).symm
      rw [hemp, hsig] at h1
      exact h1
    have hS1cmp : mu.real S1ᶜ ≤ (p : ℝ).rpow (-c) / 20 := hcompl S1 hS1 hS1good.1
    let ν : Measure ((Fin q → ℝ) × (Fin p → ℝ)) := Measure.map Prod.swap Prow
    haveI hνprob : IsProbabilityMeasure ν :=
      MeasureTheory.Measure.isProbabilityMeasure_map (μ := Prow) (f := Prod.swap)
        measurable_swap.aemeasurable
    have horlic : ∀ (X : Ω → ℝ), HasSubgaussianMGF X ⟨L, hL.le⟩ mu →
        Statlib.StatFoundation.Vocabulary.subgaussianOrliczNorm X mu ≤ ENNReal.ofReal (4 * (L + 1)) := by
      intro X hX
      exact statopia_math_node_1373677170_21fd32dd mu X L hL hX
    have hmapTν : ∀ (r : Fin nt), Measure.map (fun ω => (Ht r ω, Et r ω)) mu = ν := by
      intro r
      have h := MeasureTheory.Measure.map_map (μ := mu)
        (f := fun ω => (Et r ω, Ht r ω)) (g := Prod.swap) measurable_swap (hpairTm r)
      rw [hmapT r] at h
      exact h.symm
    have hMfν : ∀ (j : Fin p) (l : Fin q),
        PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.Mf f ν j l
          = M j l := by
      intro j l
      have h := MeasureTheory.integral_map (μ := Prow) (φ := Prod.swap)
        (f := fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l)
        measurable_swap.aemeasurable
        (((measurable_pi_apply j).comp (hf.comp measurable_fst)).mul
          ((measurable_pi_apply l).comp measurable_fst)).aestronglyMeasurable
      show (∫ z : (Fin q → ℝ) × (Fin p → ℝ), f z.1 j * z.1 l ∂ν) = M j l
      rw [h]
      exact (hMf j l).symm
    have hIntν : ∀ (j : Fin p) (l : Fin q),
        Integrable (fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l) ν := by
      intro j l
      refine (MeasureTheory.integrable_map_measure
        (μ := Prow) (f := Prod.swap)
        (g := fun z : (Fin q → ℝ) × (Fin p → ℝ) => f z.1 j * z.1 l)
        (((measurable_pi_apply j).comp (hf.comp measurable_fst)).mul
          ((measurable_pi_apply l).comp measurable_fst)).aestronglyMeasurable
        measurable_swap.aemeasurable).mpr ?_
      have h5 : (fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 j * x.2 l)
          = (fun x : (Fin p → ℝ) × (Fin q → ℝ) => (f x.2 j + x.1 j) * x.2 l) -
            fun x : (Fin p → ℝ) × (Fin q → ℝ) => x.1 j * x.2 l := by
        funext x
        simp only [Pi.sub_apply]
        ring
      show Integrable (fun x : (Fin p → ℝ) × (Fin q → ℝ) => f x.2 j * x.2 l) Prow
      rw [h5]
      exact (hIntXH j l).sub (hIntEH j l)
    have hrow : ∀ (c : ℝ), 0 ≤ c → ∀ (A : Fin p → Fin q → ℝ), (∀ i j, |A i j| ≤ c) →
        ∀ i, Real.sqrt (∑ j, (A i j) ^ 2) ≤ Real.sqrt (q : ℝ) * c := by
      intro c hc A hA i
      have h2 : ∀ j : Fin q, (A i j) ^ 2 ≤ c ^ 2 := by
        intro j
        have h3 : |A i j| * |A i j| ≤ c * c := mul_self_le_mul_self (abs_nonneg _) (hA i j)
        have e1 : (A i j) ^ 2 = |A i j| * |A i j| := by rw [← sq_abs, pow_two]
        have e2 : c ^ 2 = c * c := by rw [pow_two]
        rw [e1, e2]
        exact h3
      have h1 : ∑ j : Fin q, (A i j) ^ 2 ≤ (q : ℝ) * c ^ 2 := by
        calc ∑ j : Fin q, (A i j) ^ 2 ≤ ∑ _j : Fin q, c ^ 2 :=
              Finset.sum_le_sum (fun j _ => h2 j)
          _ = (q : ℝ) * c ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      calc Real.sqrt (∑ j : Fin q, (A i j) ^ 2) ≤ Real.sqrt ((q : ℝ) * c ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = Real.sqrt (q : ℝ) * c := by
            rw [Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq hc]
    have hqgen : ∀ (t : ℝ), Real.sqrt (q : ℝ) * (CH * Real.sqrt (Real.log (p : ℝ) / t))
        = CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / t) := by
      intro t
      have h1 : Real.sqrt (q : ℝ) * Real.sqrt (Real.log (p : ℝ) / t)
          = Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / t) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg q)]
        congr 1
        ring
      calc Real.sqrt (q : ℝ) * (CH * Real.sqrt (Real.log (p : ℝ) / t))
          = CH * (Real.sqrt (q : ℝ) * Real.sqrt (Real.log (p : ℝ) / t)) := by ring
        _ = CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / t) := by rw [h1]
    have hindTswap : iIndepFun (fun (i : Fin nt) ω => (Ht i ω, Et i ω)) mu :=
      hindTpair.comp (fun _ => Prod.swap) (fun _ => measurable_swap)
    have hbadT := _h3 p hp nt (by omega) hNH_le Ω mu ν f Et Ht hindTswap hmapTν
      hEcoord hHcoord hfHtcoord hIntE_mu hIntH_mu hIntfH_mu hE0_mu hH0_mu hfH0_mu
      (fun i j => horlic (fun ω => Et i ω j) (hSgE_mu i j))
      (fun i l => horlic (fun ω => Ht i ω l) (hSgH_mu i l))
      (fun i j => horlic (fun ω => f (Ht i ω) j) (hSgfH_mu i j))
      hIntEH_mu hEH0_mu hIntν
  
    have hcmpBE : mu.real (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent
          f Et Ht (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.Mf f ν) CH)
        ≤ (p : ℝ).rpow (-c) / 20 := by
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbadT
      rwa [ENNReal.toReal_ofReal
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (by norm_num))] at h2
    have hS4cmp : mu.real S4ᶜ ≤ (p : ℝ).rpow (-c) / 20 := by
      have hbadne : mu (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent
          f Et Ht (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.Mf f ν) CH) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbadT
      refine le_trans (MeasureTheory.measureReal_mono ?_ hbadne) hcmpBE
      intro ω hω
      by_contra hbad
      apply hω
      have hnb := hbad
      simp only [PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent,
        Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_lt] at hnb
      change ∀ (i : Fin p), Real.sqrt (∑ j : Fin q,
        ((∑ r : Fin nt, f (Ht r ω) i * Ht r ω j) / (nt : ℝ) - M i j) ^ 2)
          ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (nt : ℝ))
      have hA : ∀ (i : Fin p) (j : Fin q),
          |(∑ r : Fin nt, f (Ht r ω) i * Ht r ω j) / (nt : ℝ) - M i j|
            ≤ CH * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ)) := by
        intro i j
        have h1 := hnb.1 i j
        rw [hMfν i j] at h1
        have h2 : ((nt : ℝ)⁻¹) * (∑ r : Fin nt, f (Ht r ω) i * Ht r ω j)
            = (∑ r : Fin nt, f (Ht r ω) i * Ht r ω j) / (nt : ℝ) := by
          rw [div_eq_mul_inv, mul_comm]
        rwa [h2] at h1
      intro i
      refine le_trans (hrow (CH * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ)))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun (i' : Fin p) (j : Fin q) =>
          (∑ r : Fin nt, f (Ht r ω) i' * Ht r ω j) / (nt : ℝ) - M i' j)
        (fun i' j => hA i' j) i) ?_
      exact le_of_eq (hqgen (nt : ℝ))
    have hS6cmp : mu.real S6ᶜ ≤ (p : ℝ).rpow (-c) / 20 := by
      have hbadne : mu (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent
          f Et Ht (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.Mf f ν) CH) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbadT
      refine le_trans (MeasureTheory.measureReal_mono ?_ hbadne) hcmpBE
      intro ω hω
      by_contra hbad
      apply hω
      have hnb := hbad
      simp only [PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent,
        Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_lt] at hnb
      change ∀ (i : Fin p), Real.sqrt (∑ j : Fin q,
        ((∑ r : Fin nt, Et r ω i * Ht r ω j) / (nt : ℝ)) ^ 2)
          ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / (nt : ℝ))
      have hA : ∀ (i : Fin p) (j : Fin q),
          |(∑ r : Fin nt, Et r ω i * Ht r ω j) / (nt : ℝ)|
            ≤ CH * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ)) := by
        intro i j
        have h1 := hnb.2 i j
        have h2 : ((nt : ℝ)⁻¹) * (∑ r : Fin nt, Et r ω i * Ht r ω j)
            = (∑ r : Fin nt, Et r ω i * Ht r ω j) / (nt : ℝ) := by
          rw [div_eq_mul_inv, mul_comm]
        rwa [h2] at h1
      intro i
      refine le_trans (hrow (CH * Real.sqrt (Real.log (p : ℝ) / (nt : ℝ)))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun (i' : Fin p) (j : Fin q) => (∑ r : Fin nt, Et r ω i' * Ht r ω j) / (nt : ℝ))
        (fun i' j => hA i' j) i) ?_
      exact le_of_eq (hqgen (nt : ℝ))
    have hcardP : Fintype.card ((k : Fin K) × Fin (ns k)) = ∑ k : Fin K, ns k := by
      rw [Fintype.card_sigma]
      simp
    have eP : ((k : Fin K) × Fin (ns k)) ≃ Fin (∑ k : Fin K, ns k) :=
      Fintype.equivFinOfCardEq hcardP
    have hindSpool : iIndepFun (fun (l : Fin (∑ k : Fin K, ns k)) ω =>
        (Hs (eP.symm l).1 (eP.symm l).2 ω, Es (eP.symm l).1 (eP.symm l).2 ω)) mu :=
      ((statopia_math_node_2082055502_c6d14abe mu
        (fun (x : (k : Fin K) × Fin (ns k)) ω => (Es x.1 x.2 ω, Hs x.1 x.2 ω)) hindSpair
        eP.symm eP.symm.injective).1).comp (fun _ => Prod.swap) (fun _ => measurable_swap)
    have hmapPν : ∀ l : Fin (∑ k : Fin K, ns k),
        Measure.map (fun ω => (Hs (eP.symm l).1 (eP.symm l).2 ω,
          Es (eP.symm l).1 (eP.symm l).2 ω)) mu = ν := by
      intro l
      have h := MeasureTheory.Measure.map_map (μ := mu)
        (f := fun ω => (Es (eP.symm l).1 (eP.symm l).2 ω, Hs (eP.symm l).1 (eP.symm l).2 ω))
        (g := Prod.swap) measurable_swap (hpairSm (eP.symm l).1 (eP.symm l).2)
      rw [hmapS (eP.symm l).1 (eP.symm l).2] at h
      exact h.symm
    have hsumP : ∀ (G : (k : Fin K) → Fin (ns k) → ℝ),
        (∑ l : Fin (∑ k : Fin K, ns k), G (eP.symm l).1 (eP.symm l).2)
          = ∑ k : Fin K, ∑ r, G k r := by
      intro G
      rw [← Fintype.sum_sigma' G]
      exact Equiv.sum_comp eP.symm (fun x => G x.1 x.2)
    have hbadP := _h3 p hp (∑ k : Fin K, ns k) hpoolN_pos
      (by rw [hpool']; exact hNH_leS) Ω mu ν f
      (fun l => Es (eP.symm l).1 (eP.symm l).2)
      (fun l => Hs (eP.symm l).1 (eP.symm l).2)
      hindSpool hmapPν
      (fun i j => hEscoord (eP.symm i).1 (eP.symm i).2 j)
      (fun i l => hHscoord (eP.symm i).1 (eP.symm i).2 l)
      (fun i j => hfHscoord (eP.symm i).1 (eP.symm i).2 j)
      (fun i j => hIntEs_mu (eP.symm i).1 (eP.symm i).2 j)
      (fun i l => hIntHs_mu (eP.symm i).1 (eP.symm i).2 l)
      (fun i j => hIntfHs_mu (eP.symm i).1 (eP.symm i).2 j)
      (fun i j => hEs0_mu (eP.symm i).1 (eP.symm i).2 j)
      (fun i l => hHs0_mu (eP.symm i).1 (eP.symm i).2 l)
      (fun i j => hfHs0_mu (eP.symm i).1 (eP.symm i).2 j)
      (fun i j => horlic (fun ω => Es (eP.symm i).1 (eP.symm i).2 ω j)
        (hSgEs_mu (eP.symm i).1 (eP.symm i).2 j))
      (fun i l => horlic (fun ω => Hs (eP.symm i).1 (eP.symm i).2 ω l)
        (hSgHs_mu (eP.symm i).1 (eP.symm i).2 l))
      (fun i j => horlic (fun ω => f (Hs (eP.symm i).1 (eP.symm i).2 ω) j)
        (hSgfHs_mu (eP.symm i).1 (eP.symm i).2 j))
      (fun i j l => hIntEH_muS (eP.symm i).1 (eP.symm i).2 j l)
      (fun i j l => hEH0_muS (eP.symm i).1 (eP.symm i).2 j l)
      hIntν
    have hbadneP : mu (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent
        f (fun l => Es (eP.symm l).1 (eP.symm l).2) (fun l => Hs (eP.symm l).1 (eP.symm l).2)
        (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.Mf f ν) CH) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbadP
    have hcmpBP : mu.real (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent
        f (fun l => Es (eP.symm l).1 (eP.symm l).2) (fun l => Hs (eP.symm l).1 (eP.symm l).2)
        (PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.Mf f ν) CH)
        ≤ (p : ℝ).rpow (-c) / 20 := by
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbadP
      rwa [ENNReal.toReal_ofReal
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (by norm_num))] at h2
    have hS5cmp : mu.real S5ᶜ ≤ (p : ℝ).rpow (-c) / 20 := by
      refine le_trans (MeasureTheory.measureReal_mono ?_ hbadneP) hcmpBP
      intro ω hω
      by_contra hbad
      apply hω
      have hnb := hbad
      simp only [PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent,
        Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_lt] at hnb
      change ∀ (i : Fin p), Real.sqrt (∑ j : Fin q,
        ((∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i * Hs k r ω j) / nsTot - M i j) ^ 2)
          ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot)
      have hA : ∀ (i : Fin p) (j : Fin q),
          |(∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i * Hs k r ω j) / nsTot - M i j|
            ≤ CH * Real.sqrt (Real.log (p : ℝ) / nsTot) := by
        intro i j
        have h1 := hnb.1 i j
        rw [hMfν i j] at h1
        have hre : (∑ l : Fin (∑ k : Fin K, ns k),
              f (Hs (eP.symm l).1 (eP.symm l).2 ω) i * Hs (eP.symm l).1 (eP.symm l).2 ω j)
            = ∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i * Hs k r ω j := by
          have h := hsumP (fun (k : Fin K) (r : Fin (ns k)) => f (Hs k r ω) i * Hs k r ω j)
          simpa using h
        rw [hre] at h1
        have h2 : (((∑ k : Fin K, ns k : ℕ) : ℝ))⁻¹ *
              (∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i * Hs k r ω j)
            = (∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i * Hs k r ω j) / nsTot := by
          rw [hpool', div_eq_mul_inv, mul_comm]
        have h4 : CH * Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ))
            = CH * Real.sqrt (Real.log (p : ℝ) / nsTot) := by rw [hpool']
        rw [h2, h4] at h1
        exact h1
      intro i
      refine le_trans (hrow (CH * Real.sqrt (Real.log (p : ℝ) / nsTot))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun (i' : Fin p) (j : Fin q) =>
          (∑ k : Fin K, ∑ r : Fin (ns k), f (Hs k r ω) i' * Hs k r ω j) / nsTot - M i' j)
        (fun i' j => hA i' j) i) ?_
      exact le_of_eq (hqgen nsTot)
    have hS7cmp : mu.real S7ᶜ ≤ (p : ℝ).rpow (-c) / 20 := by
      refine le_trans (MeasureTheory.measureReal_mono ?_ hbadneP) hcmpBP
      intro ω hω
      by_contra hbad
      apply hω
      have hnb := hbad
      simp only [PaperProofTasks.job_paper_6ff987a9c5974b249aed2ac5c2c60b28.Statlib.Imported.badEvent,
        Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_lt] at hnb
      change ∀ (i : Fin p), Real.sqrt (∑ j : Fin q,
        ((∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i * Hs k r ω j) / nsTot) ^ 2)
          ≤ CH * Real.sqrt ((q : ℝ) * Real.log (p : ℝ) / nsTot)
      have hA : ∀ (i : Fin p) (j : Fin q),
          |(∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i * Hs k r ω j) / nsTot|
            ≤ CH * Real.sqrt (Real.log (p : ℝ) / nsTot) := by
        intro i j
        have h1 := hnb.2 i j
        have hre : (∑ l : Fin (∑ k : Fin K, ns k),
              Es (eP.symm l).1 (eP.symm l).2 ω i * Hs (eP.symm l).1 (eP.symm l).2 ω j)
            = ∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i * Hs k r ω j := by
          have h := hsumP (fun (k : Fin K) (r : Fin (ns k)) => Es k r ω i * Hs k r ω j)
          simpa using h
        rw [hre] at h1
        have h2 : (((∑ k : Fin K, ns k : ℕ) : ℝ))⁻¹ *
              (∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i * Hs k r ω j)
            = (∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i * Hs k r ω j) / nsTot := by
          rw [hpool', div_eq_mul_inv, mul_comm]
        have h4 : CH * Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ))
            = CH * Real.sqrt (Real.log (p : ℝ) / nsTot) := by rw [hpool']
        rw [h2, h4] at h1
        exact h1
      intro i
      refine le_trans (hrow (CH * Real.sqrt (Real.log (p : ℝ) / nsTot))
        (mul_nonneg hCH.le (Real.sqrt_nonneg _))
        (fun (i' : Fin p) (j : Fin q) =>
          (∑ k : Fin K, ∑ r : Fin (ns k), Es k r ω i' * Hs k r ω j) / nsTot)
        (fun i' j => hA i' j) i) ?_
      exact le_of_eq (hqgen nsTot)
    have hball : ∀ j : Fin 10, mu.real ((S j)ᶜ) ≤ (p : ℝ).rpow (-c) / 20 := by
      intro j
      fin_cases j
      · exact hS1cmp
      · exact hcompl S2 hS2 hS1good.2
      · have hS3good : 1 - (p : ℝ).rpow (-c) / 20 ≤ mu.real S3 := by
          have hB : ∀ a b : Fin p, |SigmaX a b| ≤ 8 * max L 1 := by
            intro a b
            rw [hSigmaX a b]
            exact statopia_math_node_49985671_e6361ae3 p q hp0 hq0 Prow f L hL
              hIntE hE0 hIntH hH0 hIntf hf0 hSgE hSgH hSgf hIntX hIntEH a b
          have hSigX : ∀ a b : Fin p,
              SigmaX a b = ∫ ω, (f (Ht ⟨0, hnt⟩ ω) + Et ⟨0, hnt⟩ ω) a *
                (f (Ht ⟨0, hnt⟩ ω) + Et ⟨0, hnt⟩ ω) b ∂mu := by
            intro a b
            have h := MeasureTheory.integral_map (μ := mu)
              (φ := fun ω => (Et ⟨0, hnt⟩ ω, Ht ⟨0, hnt⟩ ω))
              (f := fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
                (f x.2 a + x.1 a) * (f x.2 b + x.1 b))
              (hpairTm ⟨0, hnt⟩).aemeasurable
              (by rw [hmapT ⟨0, hnt⟩]; exact (hIntX a b).1)
            rw [hmapT ⟨0, hnt⟩] at h
            exact (hSigmaX a b).trans h
          have hIntXX : ∀ a b : Fin p,
              Integrable (fun ω => (f (Ht ⟨0, hnt⟩ ω) + Et ⟨0, hnt⟩ ω) a *
                (f (Ht ⟨0, hnt⟩ ω) + Et ⟨0, hnt⟩ ω) b) mu := by
            intro a b
            refine (MeasureTheory.integrable_map_measure (μ := mu)
              (f := fun ω => (Et ⟨0, hnt⟩ ω, Ht ⟨0, hnt⟩ ω))
              (g := fun x : (Fin p → ℝ) × (Fin q → ℝ) =>
                (f x.2 a + x.1 a) * (f x.2 b + x.1 b))
              (by rw [hmapT ⟨0, hnt⟩]; exact (hIntX a b).1)
              (hpairTm ⟨0, hnt⟩).aemeasurable).mp ?_
            rw [hmapT ⟨0, hnt⟩]
            exact hIntX a b
          let Ef : (Fin nt ⊕ ((k : Fin K) × Fin (ns k))) → Ω → Fin p → ℝ :=
            fun r ω => ((pooledRow Et Ht epsT Es Hs epsS r ω).1).1
          let Hf : (Fin nt ⊕ ((k : Fin K) × Fin (ns k))) → Ω → Fin q → ℝ :=
            fun r ω => ((pooledRow Et Ht epsT Es Hs epsS r ω).1).2
          have hmeasPair : ∀ r : (Fin nt ⊕ ((k : Fin K) × Fin (ns k))),
              Measurable (fun ω => (Ef r ω, Hf r ω)) := by
            intro r
            cases r with
            | inl i => exact hpairTm i
            | inr x => exact hpairSm x.1 x.2
          have hmapPair : ∀ r : (Fin nt ⊕ ((k : Fin K) × Fin (ns k))),
              Measure.map (fun ω => (Ef r ω, Hf r ω)) mu = Prow := by
            intro r
            cases r with
            | inl i => exact hmapT i
            | inr x => exact hmapS x.1 x.2
          have hIndPair : iIndepFun (fun r ω => (Ef r ω, Hf r ω)) mu :=
            hInd.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
          have hIdent : ∀ r r' : (Fin nt ⊕ ((k : Fin K) × Fin (ns k))),
              IdentDistrib (fun ω => (Ef r ω, Hf r ω))
                (fun ω => (Ef r' ω, Hf r' ω)) mu mu :=
            fun r r' => ⟨(hmeasPair r).aemeasurable, (hmeasPair r').aemeasurable,
              by rw [hmapPair r, hmapPair r']⟩
          have hres := _h2 p hp K hK nt hnt ns hns (∑ k : Fin K, ns k) rfl hpoolN_pos
            hnt_le_pool sDelta hsDelta
            (fun k j => betas k j - betaBar ns nsTot betas j) (fun k => hbeta k)
            Ω mu Ef Hf f hf
            (fun r a => by
              cases r with
              | inl i => exact hEcoord i a
              | inr x => exact hEscoord x.1 x.2 a)
            (fun r b => by
              cases r with
              | inl i => exact hHcoord i b
              | inr x => exact hHscoord x.1 x.2 b)
            (fun r a => by
              cases r with
              | inl i => exact hfHtcoord i a
              | inr x => exact hfHscoord x.1 x.2 a)
            (fun r a => by
              cases r with
              | inl i => exact hIntE_mu i a
              | inr x => exact hIntEs_mu x.1 x.2 a)
            (fun r b => by
              cases r with
              | inl i => exact hIntH_mu i b
              | inr x => exact hIntHs_mu x.1 x.2 b)
            (fun r a => by
              cases r with
              | inl i => exact hIntfH_mu i a
              | inr x => exact hIntfHs_mu x.1 x.2 a)
            hIndPair hIdent
            (fun r a => by
              cases r with
              | inl i => exact hE0_mu i a
              | inr x => exact hEs0_mu x.1 x.2 a)
            (fun r b => by
              cases r with
              | inl i => exact hH0_mu i b
              | inr x => exact hHs0_mu x.1 x.2 b)
            (fun r a => by
              cases r with
              | inl i => exact hfH0_mu i a
              | inr x => exact hfHs0_mu x.1 x.2 a)
            (fun r a => by
              cases r with
              | inl i => exact hSgE_mu i a
              | inr x => exact hSgEs_mu x.1 x.2 a)
            (fun r b => by
              cases r with
              | inl i => exact hSgH_mu i b
              | inr x => exact hSgHs_mu x.1 x.2 b)
            (fun r a => by
              cases r with
              | inl i => exact hSgfH_mu i a
              | inr x => exact hSgfHs_mu x.1 x.2 a)
            (fun r a b => by
              cases r with
              | inl i => exact hEH0_mu i a b
              | inr x => exact hEH0_muS x.1 x.2 a b)
            (fun r a b => by
              cases r with
              | inl i => exact hIntEH_mu i a b
              | inr x => exact hIntEH_muS x.1 x.2 a b)
            SigmaX hSigX hIntXX hB (by rw [hpool']; exact hNdelta_leS)
          refine le_trans hres ?_
          refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω ⊢
          intro i
          have h1 := hω i
          have hEr : ∀ (k : Fin K) (r : Fin (ns k)), Ef (Sum.inr ⟨k, r⟩) ω = Es k r ω :=
            fun k r => rfl
          have hHr : ∀ (k : Fin K) (r : Fin (ns k)), Hf (Sum.inr ⟨k, r⟩) ω = Hs k r ω :=
            fun k r => rfl
          have hErP : ∀ (k : Fin K) (r : Fin (ns k)),
              ((pooledRow Et Ht epsT Es Hs epsS (Sum.inr ⟨k, r⟩) ω).1).1 = Es k r ω :=
            fun k r => rfl
          have hHrP : ∀ (k : Fin K) (r : Fin (ns k)),
              ((pooledRow Et Ht epsT Es Hs epsS (Sum.inr ⟨k, r⟩) ω).1).2 = Hs k r ω :=
            fun k r => rfl
          simp only [hEr, hHr, hErP, hHrP, Pi.add_apply] at h1
          have hkey : ∀ (S Sig del N : ℝ), N ≠ 0 →
              (S - N * Sig) * del = N * ((S / N - Sig) * del) := by
            intro S Sig del N hN
            field_simp [hN]
          have hpush : ∀ k : Fin K,
              (∑ b : Fin p, ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) *
                  (f (Hs k r ω) b + Es k r ω b)) - (ns k : ℝ) * SigmaX i b)
                * (betas k b - betaBar ns nsTot betas b))
              = (ns k : ℝ) * ∑ b : Fin p,
                  ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) *
                      (f (Hs k r ω) b + Es k r ω b)) / (ns k : ℝ) - SigmaX i b)
                    * (betas k b - betaBar ns nsTot betas b) := by
            intro k
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun b _ => hkey _ _ _ _ (hns_ne k))
          have hbridge : (↑(∑ k : Fin K, ns k) : ℝ)⁻¹ *
              (∑ k : Fin K, ∑ b : Fin p,
                ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) *
                    (f (Hs k r ω) b + Es k r ω b)) - (ns k : ℝ) * SigmaX i b)
                  * (betas k b - betaBar ns nsTot betas b))
              = (∑ k : Fin K, (ns k : ℝ) * ∑ b : Fin p,
                  ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) *
                      (f (Hs k r ω) b + Es k r ω b)) / (ns k : ℝ) - SigmaX i b)
                    * (betas k b - betaBar ns nsTot betas b)) / nsTot := by
            have hA : (∑ k : Fin K, ∑ b : Fin p,
                ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) *
                    (f (Hs k r ω) b + Es k r ω b)) - (ns k : ℝ) * SigmaX i b)
                  * (betas k b - betaBar ns nsTot betas b))
                = ∑ k : Fin K, (ns k : ℝ) * ∑ b : Fin p,
                    ((∑ r : Fin (ns k), (f (Hs k r ω) i + Es k r ω i) *
                        (f (Hs k r ω) b + Es k r ω b)) / (ns k : ℝ) - SigmaX i b)
                      * (betas k b - betaBar ns nsTot betas b) :=
              Finset.sum_congr rfl (fun k _ => hpush k)
            rw [hA, hpool', div_eq_inv_mul]
          have hconst : Cdelta * sDelta *
              Real.sqrt (Real.log (p : ℝ) / ((∑ k : Fin K, ns k : ℕ) : ℝ))
              = Cdelta * sDelta * aSCoef p nsTot := by rw [haS_eq]
          rw [hbridge, hconst] at h1
          exact h1
        exact hcompl S3 hS3 hS3good
      · exact hS4cmp
      · exact hS5cmp
      · exact hS6cmp
      · exact hS7cmp
      · exact hS8cmp
      · exact hS9cmp
      · exact hS10cmp
    exact hfinal S hSall hball hsub
  · exact ⟨hω.1, hω.2.1⟩
  /- @proof-region region.root.3206ac050fd2 end -/

end

end Statlib.Imported

-- Paper root revision c5fc1632-b848-4e23-bfa1-6724505d389c

