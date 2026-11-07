import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1649031325_12d7295c_13e7bff5
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1967109576_c7239acb_4f2497e8
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_2194576110_d2ad0cef_60d45604
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_3430447628_ae1e147f_4d81461a
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_911816952_4086d22b_a7efc4ca

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf




open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4252936244_9b4dbd57 : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p) (hlogp : 0 < Real.log (p : ℝ))
    (hd : delta n m ≠ 0)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hGmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, G i ω j ∂P = muY j)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (phi1 phi2 : ℝ) (hphi1 : 1 ≤ phi1) (hphi2 : 1 ≤ phi2)
    (y : Fin p → ℝ)
    (phi0 : ℝ → ℝ) (hphi0_cont : ContDiff ℝ 3 phi0)
    (hphi0_left : ∀ z : ℝ, z ≤ 0 → phi0 z = 1)
    (hphi0_right : ∀ z : ℝ, 1 ≤ z → phi0 z = 0)
    (hphi0_range : ∀ z : ℝ, phi0 z ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (i : Fin m) (j : Fin p),
    let phi : ℝ := min phi1 phi2
    let beta : ℝ := phi * Real.log (p : ℝ)
    let kap : (Fin p → ℝ) → ℝ := fun w =>
      phi0 (phi * (beta⁻¹ * Real.log (∑ q : Fin p, Real.exp (beta * (w q - y q)))))
    let Zss : Ω × Ω → Fin p → ℝ := fun x k =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        (Real.sqrt t *
            (Real.sqrt v * (Y i x.1 k - muY k) + Real.sqrt (1 - v) * (G i x.1 k - muY k))
          + Real.sqrt (1 - t) * (G i x.2 k - muY k))
    let Zrest : Ω × Ω → Fin p → ℝ := fun x k =>
      (∑ i' : Fin n,
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t *
              (Real.sqrt v * (X i' x.1 k - muX k) + Real.sqrt (1 - v) * (F i' x.1 k - muX k))
            + Real.sqrt (1 - t) * (F i' x.2 k - muX k)))
      + (∑ i' : Fin m, if i' = i then 0 else
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t *
                (Real.sqrt v * (Y i' x.1 k - muY k) + Real.sqrt (1 - v) * (G i' x.1 k - muY k))
              + Real.sqrt (1 - t) * (G i' x.2 k - muY k)))
    let Psi : Ω × Ω → ℝ := fun x => (fderiv ℝ kap (Zrest x)) (Pi.single j (1 : ℝ))
    let D : Ω × Ω → ℝ := fun x =>
      (Real.sqrt (m : ℝ))⁻¹ * delta n m *
        ((2 * Real.sqrt t)⁻¹ *
            (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
          - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j))
    Measurable Psi ∧
      (∃ C : ℝ, ∀ x : Ω × Ω, |Psi x| ≤ C) ∧
      IndepFun Psi (fun x : Ω × Ω => (Y i x.1, (G i x.1, G i x.2))) (P.prod P) ∧
      ∫ x, Psi x * D x ∂(P.prod P) = 0 := by
  /- @proof-region region.target-node.session.ec1044cf2c234b33 begin -/
  intro Ω mΩ P hP n m p delta muX muY X Y F G hn hm hp hlogp hd
    hXm hYm hFm hGm hindep hYmean hGmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov
    v hv0 hv1 phi1 phi2 hphi1 hphi2 y phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
    t ht0 ht1 i j
  dsimp only
  set phi : ℝ := min phi1 phi2 with hphi
  set beta : ℝ := phi * Real.log (p : ℝ) with hbeta
  set kap : (Fin p → ℝ) → ℝ := fun w => phi0 (phi * (beta⁻¹ * Real.log (∑ q : Fin p, Real.exp (beta * (w q - y q))))) with hkap
  set Zss : Ω × Ω → Fin p → ℝ := fun x k =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      (Real.sqrt t *
          (Real.sqrt v * (Y i x.1 k - muY k) + Real.sqrt (1 - v) * (G i x.1 k - muY k))
        + Real.sqrt (1 - t) * (G i x.2 k - muY k)) with hZss
  set Zrest : Ω × Ω → Fin p → ℝ := fun x k =>
    (∑ i' : Fin n,
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt t *
            (Real.sqrt v * (X i' x.1 k - muX k) + Real.sqrt (1 - v) * (F i' x.1 k - muX k))
          + Real.sqrt (1 - t) * (F i' x.2 k - muX k)))
    + (∑ i' : Fin m, if i' = i then 0 else
        (Real.sqrt (m : ℝ))⁻¹ * delta n m *
          (Real.sqrt t *
              (Real.sqrt v * (Y i' x.1 k - muY k) + Real.sqrt (1 - v) * (G i' x.1 k - muY k))
            + Real.sqrt (1 - t) * (G i' x.2 k - muY k))) with hZrest
  set Psi : Ω × Ω → ℝ := fun x => (fderiv ℝ kap (Zrest x)) (Pi.single j (1 : ℝ)) with hPsi
  set D : Ω × Ω → ℝ := fun x =>
    (Real.sqrt (m : ℝ))⁻¹ * delta n m *
      ((2 * Real.sqrt t)⁻¹ *
          (Real.sqrt v * (Y i x.1 j - muY j) + Real.sqrt (1 - v) * (G i x.1 j - muY j))
        - (2 * Real.sqrt (1 - t))⁻¹ * (G i x.2 j - muY j)) with hD
  have hp2 : 2 ≤ p := by
    by_contra h
    push_neg at h
    have hp1 : p = 1 := by omega
    rw [hp1] at hlogp
    simp at hlogp
  have hphi_ge : 1 ≤ phi := by
    rw [hphi]
    exact le_min hphi1 hphi2
  obtain ⟨hkap_cont, _, _, _, _, _, _, _⟩ :=
    statopia_math_node_2194576110_d2ad0cef p hp2 phi hphi_ge phi0 hphi0_cont hphi0_left hphi0_right hphi0_range y
  have hkap_cont' : ContDiff ℝ 3 kap := by
    simpa [hkap, hbeta] using hkap_cont
  obtain ⟨Cκ, hCκ_nonneg, hCκ⟩ :=
    statopia_math_node_1967109576_c7239acb phi0 hphi0_cont hphi0_left hphi0_right hphi0_range
  have hX_meas (i' : Fin n) (k : Fin p) : Measurable (fun x : Ω × Ω => X i' x.1 k) :=
    ((measurable_pi_iff.mp (hXm i')) k).comp measurable_fst
  have hF_meas1 (i' : Fin n) (k : Fin p) : Measurable (fun x : Ω × Ω => F i' x.1 k) :=
    ((measurable_pi_iff.mp (hFm i')) k).comp measurable_fst
  have hF_meas2 (i' : Fin n) (k : Fin p) : Measurable (fun x : Ω × Ω => F i' x.2 k) :=
    ((measurable_pi_iff.mp (hFm i')) k).comp measurable_snd
  have hY_meas (i' : Fin m) (k : Fin p) : Measurable (fun x : Ω × Ω => Y i' x.1 k) :=
    ((measurable_pi_iff.mp (hYm i')) k).comp measurable_fst
  have hG_meas1 (i' : Fin m) (k : Fin p) : Measurable (fun x : Ω × Ω => G i' x.1 k) :=
    ((measurable_pi_iff.mp (hGm i')) k).comp measurable_fst
  have hG_meas2 (i' : Fin m) (k : Fin p) : Measurable (fun x : Ω × Ω => G i' x.2 k) :=
    ((measurable_pi_iff.mp (hGm i')) k).comp measurable_snd
  have hZss_summand_meas (i' : Fin m) (k : Fin p) :
      Measurable (fun x : Ω × Ω =>
        if i' = i then (0 : ℝ)
        else
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t *
                (Real.sqrt v * (Y i' x.1 k - muY k) + Real.sqrt (1 - v) * (G i' x.1 k - muY k))
              + Real.sqrt (1 - t) * (G i' x.2 k - muY k))) := by
    by_cases h : i' = i
    · simp [h]
    · simp [h]
      fun_prop
  have hZx_summand_meas (i' : Fin n) (k : Fin p) :
      Measurable (fun x : Ω × Ω =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t *
              (Real.sqrt v * (X i' x.1 k - muX k) + Real.sqrt (1 - v) * (F i' x.1 k - muX k))
            + Real.sqrt (1 - t) * (F i' x.2 k - muX k))) := by
    fun_prop
  have hZrest_meas : Measurable Zrest := by
    rw [measurable_pi_iff]
    intro k
    rw [hZrest]
    have h1 : Measurable (fun x : Ω × Ω =>
        ∑ i' : Fin n,
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt t *
                (Real.sqrt v * (X i' x.1 k - muX k) + Real.sqrt (1 - v) * (F i' x.1 k - muX k))
              + Real.sqrt (1 - t) * (F i' x.2 k - muX k))) := by
      fun_prop
    have h2 : Measurable (fun x : Ω × Ω =>
        ∑ i' : Fin m, if i' = i then (0 : ℝ) else
          (Real.sqrt (m : ℝ))⁻¹ * delta n m *
            (Real.sqrt t *
                (Real.sqrt v * (Y i' x.1 k - muY k) + Real.sqrt (1 - v) * (G i' x.1 k - muY k))
              + Real.sqrt (1 - t) * (G i' x.2 k - muY k))) := by
      fun_prop
    exact h1.add h2
  have hPsi_meas : Measurable Psi := by
    have hderiv : Measurable (fun w : Fin p → ℝ => (fderiv ℝ kap w) (Pi.single j (1 : ℝ))) :=
      measurable_fderiv_apply_const ℝ kap (Pi.single j (1 : ℝ))
    rw [hPsi]
    exact hderiv.comp hZrest_meas
  have hPsi_bound : ∃ C : ℝ, ∀ x : Ω × Ω, |Psi x| ≤ C := by
    refine ⟨Cκ * phi, ?_⟩
    intro x
    rw [hPsi]
    simpa [hkap, hbeta] using hCκ p hp2 phi hphi_ge y (Zrest x) j
  refine ⟨hPsi_meas, hPsi_bound, ?_, ?_⟩
  · have hPsi_ind : IndepFun Psi (fun x : Ω × Ω => (Y i x.1, (G i x.1, G i x.2))) (P.prod P) := by
      simpa [hPsi, hZrest] using
        @statopia_math_node_3430447628_ae1e147f Ω mΩ P hP n m p delta muX muY X Y F G
          hXm hYm hFm hGm hindep kap (hkap_cont'.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) v t i j
    exact hPsi_ind
  · have hYint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => Y i ω j) P := by
      intro i j
      have h_meas : Measurable (fun ω => Y i ω j) :=
        (measurable_pi_iff.mp (hYm i)) j
      have h_dom : Integrable (fun ω => |muY j| + (1 + |Y i ω j - muY j| ^ 3)) P :=
        (integrable_const |muY j|).add ((integrable_const (1 : ℝ)).add (hY3 i j))
      refine h_dom.mono' h_meas.aestronglyMeasurable ?_
      filter_upwards with ω
      have h_nonneg : 0 ≤ |Y i ω j - muY j| := abs_nonneg _
      have h1 : |Y i ω j| ≤ |Y i ω j - muY j| + |muY j| := by
        have h_eq : Y i ω j = (Y i ω j - muY j) + muY j := by ring
        conv_lhs => rw [h_eq]
        exact abs_add_le _ _
      have h2 : |Y i ω j - muY j| ≤ 1 + |Y i ω j - muY j| ^ 3 := by
        by_cases hx : |Y i ω j - muY j| ≤ 1
        · nlinarith [pow_nonneg h_nonneg 3]
        · push_neg at hx
          have h_sq : 1 ≤ |Y i ω j - muY j| ^ 2 := by
            nlinarith [sq_nonneg (|Y i ω j - muY j| - 1)]
          have h_cube : |Y i ω j - muY j| ≤ |Y i ω j - muY j| ^ 3 := by
            nlinarith [mul_nonneg h_nonneg (sub_nonneg.mpr h_sq)]
          nlinarith [h_cube, pow_nonneg h_nonneg 3]
      have h_abs : |Y i ω j| ≤ |muY j| + (1 + |Y i ω j - muY j| ^ 3) := by
        nlinarith [h1, h2]
      simpa using h_abs
    have hGint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j) P := by
      intro i j
      have h_meas : Measurable (fun ω => G i ω j) :=
        (measurable_pi_iff.mp (hGm i)) j
      have h_dom : Integrable (fun ω => |muY j| + (1 + |G i ω j - muY j| ^ 3)) P :=
        (integrable_const |muY j|).add ((integrable_const (1 : ℝ)).add (hG3 i j))
      refine h_dom.mono' h_meas.aestronglyMeasurable ?_
      filter_upwards with ω
      have h_nonneg : 0 ≤ |G i ω j - muY j| := abs_nonneg _
      have h1 : |G i ω j| ≤ |G i ω j - muY j| + |muY j| := by
        have h_eq : G i ω j = (G i ω j - muY j) + muY j := by ring
        conv_lhs => rw [h_eq]
        exact abs_add_le _ _
      have h2 : |G i ω j - muY j| ≤ 1 + |G i ω j - muY j| ^ 3 := by
        by_cases hx : |G i ω j - muY j| ≤ 1
        · nlinarith [pow_nonneg h_nonneg 3]
        · push_neg at hx
          have h_sq : 1 ≤ |G i ω j - muY j| ^ 2 := by
            nlinarith [sq_nonneg (|G i ω j - muY j| - 1)]
          have h_cube : |G i ω j - muY j| ≤ |G i ω j - muY j| ^ 3 := by
            nlinarith [mul_nonneg h_nonneg (sub_nonneg.mpr h_sq)]
          nlinarith [h_cube, pow_nonneg h_nonneg 3]
      have h_abs : |G i ω j| ≤ |muY j| + (1 + |G i ω j - muY j| ^ 3) := by
        nlinarith [h1, h2]
      simpa using h_abs
    have hPsi_ind : IndepFun Psi (fun x : Ω × Ω => (Y i x.1, (G i x.1, G i x.2))) (P.prod P) := by
      simpa [hPsi, hZrest] using
        @statopia_math_node_3430447628_ae1e147f Ω mΩ P hP n m p delta muX muY X Y F G
          hXm hYm hFm hGm hindep kap (hkap_cont'.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) v t i j
    have h := statopia_math_node_911816952_4086d22b Ω P m p (delta n m) muY Y G
      hYm hGm hYmean hGmean hYint hGint v t hv0 hv1 ht0 ht1 i j Psi hPsi_meas hPsi_bound hPsi_ind
    simpa [hD] using h
  /- @proof-region region.target-node.session.ec1044cf2c234b33 end -/

end

end Statlib.Imported

