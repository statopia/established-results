import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_1214593279_6b91f964_839e3043
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_18671509_e0d2ff36_418b4aba

namespace PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261108t120211266248z_prior_learning33.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_189267838_542a0222 : ∀ (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [MeasurableSpace U] [BorelSpace U]
    (e : HilbertBasis ℕ ℝ U) (c : ℕ → ℝ) (hc_pos : ∀ k : ℕ, 0 < c k)
    (mu nu : Measure U) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (m_mu m_nu : U)
    (hmarg_mu : ∀ n : ℕ,
      MeasureTheory.Measure.map (fun u : U => fun i : Fin n => inner ℝ (e i) u) mu
        = MeasureTheory.Measure.pi
            (fun i : Fin n =>
              ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩))
    (hsigma2 : Summable (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))
    (hsum : ∀ᵐ u ∂mu,
      Summable (fun k : ℕ => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu)))
    (hcyl : ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin n,
                    ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) * (inner ℝ (e i) u - inner ℝ (e i) m_mu))
                      / c i)
                  - (∑ i : Fin n, (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i)))) ∂mu),
    ∀ (n : ℕ) (C : Set (Fin n → ℝ)), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = (mu.withDensity (fun u : U =>
            ENNReal.ofReal
              (Real.exp
                ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
                  - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))))
          ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C) := by
  /- @proof-region region.target-node.session.3b0afdebe8f1acdc begin -/
  intro U _ _ _ _ _ _ e c hc_pos mu nu _ _ m_mu m_nu hmarg_mu hsigma2 hsum hcyl n C hC
  have hmeas : Measurable (fun u : U => fun i : Fin n => inner ℝ (e i) u) :=
    measurable_pi_iff.mpr fun i =>
      (continuous_inner.comp (continuous_const.prodMk continuous_id)).measurable
  have hA : MeasurableSet ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C) :=
    hC.preimage hmeas
  have hpt_gen : ∀ (m : ℕ) (v : U),
      ENNReal.ofReal
          (Real.exp
            ((∑ i : Fin m,
                ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) *
                    (inner ℝ (e i) v - inner ℝ (e i) m_mu))
                  / c i)
              - (∑ i : Fin m,
                  (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i))))
        = ENNReal.ofReal
            (Real.exp
              ((∑ i : Fin m,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (v - m_mu))
                - (∑ i : Fin m,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) := by
    intro m v
    have hid :
        ((∑ i : Fin m,
              ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) *
                  (inner ℝ (e i) v - inner ℝ (e i) m_mu))
                / c i)
            - (∑ i : Fin m,
                (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i)))
          = ((∑ i : Fin m,
                (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (v - m_mu))
              - (∑ i : Fin m,
                  (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2) := by
      simp only [inner_sub_right]
      have h1 :
          (∑ i : Fin m,
              ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) *
                  (inner ℝ (e i) v - inner ℝ (e i) m_mu))
                / c i)
            = ∑ i : Fin m,
                (c i)⁻¹ * (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) *
                  (inner ℝ (e i) v - inner ℝ (e i) m_mu) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_inv_mul]
        ring
      have h2 :
          (∑ i : Fin m, (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i))
            = (∑ i : Fin m,
                (c i)⁻¹ * (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        have hi : c i ≠ 0 := ne_of_gt (hc_pos i)
        field_simp [hi]
      rw [h1, h2]
    rw [hid]
  have hlint1 :
      ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
          ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin n,
                    ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) *
                        (inner ℝ (e i) u - inner ℝ (e i) m_mu))
                      / c i)
                  - (∑ i : Fin n,
                      (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i)))) ∂mu
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin n,
                    (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                  - (∑ i : Fin n,
                      (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) ∂mu :=
    lintegral_congr (hpt_gen n)
  have h_one_gen : ∀ m : ℕ,
      (∫⁻ u : U,
          ENNReal.ofReal
            (Real.exp
              ((∑ i : Fin m,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                - (∑ i : Fin m,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) ∂mu) = 1 := by
    intro m
    have h1 := hcyl m (Set.univ : Set (Fin m → ℝ)) MeasurableSet.univ
    rw [Set.preimage_univ, measure_univ] at h1
    have h2 :
        (∫⁻ u : U,
            ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin m,
                    ((inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) *
                        (inner ℝ (e i) u - inner ℝ (e i) m_mu))
                      / c i)
                  - (∑ i : Fin m,
                      (inner ℝ (e i) m_nu - inner ℝ (e i) m_mu) ^ 2 / (2 * c i)))) ∂mu) = 1 := by
      simpa using h1.symm
    rw [← h2]
    exact (lintegral_congr (hpt_gen m)).symm
  have hconv :
      ∀ᵐ u ∂mu,
        Tendsto
          (fun m : ℕ =>
            Real.exp
              ((∑ i ∈ Finset.range m,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                - (∑ i ∈ Finset.range m,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))
          atTop
          (𝓝 (Real.exp
            ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
              - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))) := by
    filter_upwards [hsum] with u hu
    have h1 :
        Tendsto
          (fun m : ℕ =>
            ∑ i ∈ Finset.range m,
              (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
          atTop
          (𝓝 (∑' k : ℕ,
            (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))) :=
      hu.hasSum.tendsto_sum_nat
    have h2 :
        Tendsto
          (fun m : ℕ => ∑ i ∈ Finset.range m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2)
          atTop
          (𝓝 (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)) :=
      hsigma2.hasSum.tendsto_sum_nat
    have h3 := h1.sub (h2.div_const 2)
    exact (Real.continuous_exp.tendsto _).comp h3
  have hstep3 : ∀ (n m : ℕ), n ≤ m → ∀ C : Set (Fin n → ℝ), MeasurableSet C →
      nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin m,
                    (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                  - (∑ i : Fin m,
                      (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) ∂mu := by
    intro n m hnm C hC
    have hrm : Measurable (fun x : Fin m → ℝ => fun i : Fin n => x (Fin.castLE hnm i)) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply (Fin.castLE hnm i)
    have hms : MeasurableSet
        ((fun x : Fin m → ℝ => fun i : Fin n => x (Fin.castLE hnm i)) ⁻¹' C) :=
      hC.preimage hrm
    have hfun : (fun u : U => fun i : Fin n => inner ℝ (e i) u)
        = (fun x : Fin m → ℝ => fun i : Fin n => x (Fin.castLE hnm i)) ∘
            (fun u : U => fun i : Fin m => inner ℝ (e i) u) := by
      funext u i
      rfl
    rw [hfun, Set.preimage_comp, hcyl m _ hms]
    exact lintegral_congr (hpt_gen m)
  have hL2P :
      ∫⁻ x : Fin n → ℝ,
          (ENNReal.ofReal
            (Real.exp
              ((∑ i : Fin n,
                  ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) * (x i - inner ℝ (e i) m_mu))
                - (∑ i : Fin n,
                    ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i) / 2))) ^ 2
          ∂(MeasureTheory.Measure.pi (fun i : Fin n =>
              ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩))
        = ENNReal.ofReal
            (Real.exp (∑ i : Fin n,
              ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i)) :=
    statopia_math_node_18671509_e0d2ff36 n c
      (fun k : ℕ => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu))
      (fun k : ℕ => inner ℝ (e k) m_mu) hc_pos
  have hsummand : ∀ i : Fin n,
      ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i
        = (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2 := by
    intro i
    have hi : c i ≠ 0 := ne_of_gt (hc_pos i)
    calc ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i
        = (c i)⁻¹ * ((c i)⁻¹ * c i) * (inner ℝ (e i) (m_nu - m_mu)) ^ 2 := by ring
      _ = (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2 := by
            rw [inv_mul_cancel₀ hi, mul_one]
  have hL2P' :
      ∫⁻ x : Fin n → ℝ,
          (ENNReal.ofReal
            (Real.exp
              ((∑ i : Fin n,
                  ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) * (x i - inner ℝ (e i) m_mu))
                - (∑ i : Fin n,
                    ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i) / 2))) ^ 2
          ∂(MeasureTheory.Measure.pi (fun i : Fin n =>
              ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩))
        = ENNReal.ofReal
            (Real.exp (∑ i : Fin n,
              (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2)) := by
    rw [hL2P, Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hsq_exp : ∀ E : ℝ,
      (ENNReal.ofReal (Real.exp E)) ^ 2 = ENNReal.ofReal (Real.exp (2 * E)) := by
    intro E
    rw [← ENNReal.ofReal_pow (le_of_lt (Real.exp_pos E)) 2]
    rw [show Real.exp E ^ 2 = Real.exp (2 * E) from by
      rw [sq, ← Real.exp_add, show E + E = 2 * E by ring]]
  have hrange : ∀ (m : ℕ) (v : U),
      (∑ i : Fin m, (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (v - m_mu))
        = ∑ i ∈ Finset.range m,
            (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (v - m_mu) := by
    intro m v
    exact Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (v - m_mu)) m
  have hrange2 : ∀ m : ℕ,
      (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2)
        = ∑ i ∈ Finset.range m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2 := by
    intro m
    exact Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) m
  have hsq_dens : ∀ v : U,
      (ENNReal.ofReal
          (Real.exp
            ((∑ i : Fin n,
                (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (v - m_mu))
              - (∑ i : Fin n,
                  (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))) ^ 2
        = ENNReal.ofReal
            (Real.exp (2 * ((∑ i : Fin n,
                (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (v - m_mu))
              - (∑ i : Fin n,
                  (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))) :=
    fun v => hsq_exp _
  have hlint2 :
      ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
          ENNReal.ofReal
            (Real.exp
              ((∑ i : Fin n,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                - (∑ i : Fin n,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) ∂mu
        = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal
              (Real.exp
                ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
                  - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2)) ∂mu := by
    have hmeas_m : ∀ m : ℕ, Measurable (fun u : U => fun i : Fin m => inner ℝ (e i) u) := by
      intro m
      exact measurable_pi_iff.mpr fun i =>
        (continuous_inner.comp (continuous_const.prodMk continuous_id)).measurable
    have hsummand_gen : ∀ k : ℕ,
        ((c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu)) ^ 2 * c k
          = (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2 := by
      intro k
      have hk : c k ≠ 0 := ne_of_gt (hc_pos k)
      calc ((c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu)) ^ 2 * c k
          = (c k)⁻¹ * ((c k)⁻¹ * c k) * (inner ℝ (e k) (m_nu - m_mu)) ^ 2 := by ring
        _ = (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2 := by
              rw [inv_mul_cancel₀ hk, mul_one]
    have hmapT_gen : ∀ (m : ℕ) (G : (Fin m → ℝ) → ENNReal), Measurable G →
        (∫⁻ u : U, G (fun i : Fin m => inner ℝ (e i) u) ∂mu)
          = ∫⁻ x : Fin m → ℝ, G x ∂(MeasureTheory.Measure.map
              (fun u : U => fun i : Fin m => inner ℝ (e i) u) mu) := by
      intro m G hG
      exact (MeasureTheory.lintegral_map hG (hmeas_m m)).symm
    have hG_meas_gen : ∀ m : ℕ, Measurable (fun x : Fin m → ℝ =>
        (ENNReal.ofReal
          (Real.exp
            ((∑ i : Fin m,
                ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) * (x i - inner ℝ (e i) m_mu))
              - (∑ i : Fin m,
                  ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i) / 2))) ^ 2) := by
      intro m
      measurability
    have hpt2_gen : ∀ (m : ℕ) (u : U),
        (ENNReal.ofReal
            (Real.exp
              ((∑ i : Fin m,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                - (∑ i : Fin m,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))) ^ 2
          = (fun x : Fin m → ℝ =>
              (ENNReal.ofReal
                (Real.exp
                  ((∑ i : Fin m,
                      ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) * (x i - inner ℝ (e i) m_mu))
                    - (∑ i : Fin m,
                        ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i) / 2))) ^ 2)
            (fun i : Fin m => inner ℝ (e i) u) := by
      intro m u
      simp only [hsummand_gen]
      simp only [inner_sub_right]
    have hL2P_gen : ∀ m : ℕ,
        ∫⁻ x : Fin m → ℝ,
            (ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin m,
                    ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) * (x i - inner ℝ (e i) m_mu))
                  - (∑ i : Fin m,
                      ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i) / 2))) ^ 2
            ∂(MeasureTheory.Measure.pi (fun i : Fin m =>
                ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩))
          = ENNReal.ofReal
              (Real.exp (∑ i : Fin m,
                ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i)) := by
      intro m
      exact statopia_math_node_18671509_e0d2ff36 m c
        (fun k : ℕ => (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu))
        (fun k : ℕ => inner ℝ (e k) m_mu) hc_pos
    have hL2P'_gen : ∀ m : ℕ,
        ∫⁻ x : Fin m → ℝ,
            (ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin m,
                    ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) * (x i - inner ℝ (e i) m_mu))
                  - (∑ i : Fin m,
                      ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i) / 2))) ^ 2
            ∂(MeasureTheory.Measure.pi (fun i : Fin m =>
                ProbabilityTheory.gaussianReal (inner ℝ (e i) m_mu) ⟨c i, le_of_lt (hc_pos i)⟩))
          = ENNReal.ofReal
              (Real.exp (∑ i : Fin m,
                (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2)) := by
      intro m
      rw [hL2P_gen m]
      simp only [hsummand_gen]
    have hL2mu_gen : ∀ m : ℕ,
        (∫⁻ u : U,
            (ENNReal.ofReal
              (Real.exp
                ((∑ i : Fin m,
                    (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                  - (∑ i : Fin m,
                      (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))) ^ 2 ∂mu)
          = ENNReal.ofReal
              (Real.exp (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2)) := by
      intro m
      rw [lintegral_congr (hpt2_gen m)]
      rw [hmapT_gen m (fun x : Fin m → ℝ =>
        (ENNReal.ofReal
          (Real.exp
            ((∑ i : Fin m,
                ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) * (x i - inner ℝ (e i) m_mu))
              - (∑ i : Fin m,
                  ((c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu)) ^ 2 * c i) / 2))) ^ 2) (hG_meas_gen m)]
      rw [hmarg_mu m]
      exact hL2P'_gen m
    have hexp_meas : ∀ m : ℕ, Measurable (fun u : U =>
        (∑ i : Fin m,
            (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
          - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2) := by
      intro m
      have hinner : ∀ i : Fin m, Measurable (fun u : U => inner ℝ (e i) (u - m_mu)) :=
        fun i =>
          (continuous_inner.comp
            (continuous_const.prodMk (continuous_id.sub continuous_const))).measurable
      exact (Finset.measurable_sum Finset.univ
        (fun i (_ : i ∈ Finset.univ) => measurable_const.mul (hinner i))).sub measurable_const
    have hdens_real_meas : ∀ m : ℕ, Measurable (fun u : U =>
        Real.exp
          ((∑ i : Fin m,
              (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
            - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) :=
      fun m => Real.continuous_exp.measurable.comp (hexp_meas m)
    have h_two_exp : ∀ (m : ℕ) (u : U),
        (Real.exp
          ((∑ i : Fin m,
              (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
            - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) ^ 2
          = Real.exp (2 * ((∑ i : Fin m,
              (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
            - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) := by
      intro m u
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have h_int_sq : ∀ m : ℕ, Integrable (fun u : U =>
        Real.exp (2 * ((∑ i : Fin m,
            (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
          - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))) mu := by
      intro m
      have hmeas2 : Measurable (fun u : U =>
          Real.exp (2 * ((∑ i : Fin m,
              (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
            - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))) :=
        Real.continuous_exp.measurable.comp (measurable_const.mul (hexp_meas m))
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas2.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)).mp ?_
      rw [lintegral_congr (fun u : U => (hsq_exp ((∑ i : Fin m,
          (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
        - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)).symm)]
      rw [hL2mu_gen m]
      exact ne_of_lt ENNReal.ofReal_lt_top
    have hconv_fin : ∀ᵐ u ∂mu,
        Tendsto
          (fun m : ℕ =>
            Real.exp
              ((∑ i : Fin m,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                - (∑ i : Fin m,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))
          atTop
          (𝓝 (Real.exp
            ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
              - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2))) := by
      filter_upwards [hconv] with u hu
      have heq : (fun m : ℕ =>
            Real.exp
              ((∑ i : Fin m,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                - (∑ i : Fin m,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2))
          = (fun m : ℕ =>
            Real.exp
              ((∑ i ∈ Finset.range m,
                  (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
                - (∑ i ∈ Finset.range m,
                    (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) := by
        funext m
        rw [hrange m u, hrange2 m]
      rw [heq]
      exact hu
    have h_K_real : ∀ m : ℕ,
        (∫ u : U,
            Real.exp (2 * ((∑ i : Fin m,
                (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
              - (∑ i : Fin m,
                  (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)) ∂mu)
          = Real.exp (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) := by
      intro m
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
        (h_int_sq m).aestronglyMeasurable]
      rw [lintegral_congr (fun u : U => (hsq_exp ((∑ i : Fin m,
          (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
        - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)).symm)]
      rw [hL2mu_gen m]
      exact ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))
    let F : ℕ → U → ℝ := fun (m : ℕ) (u : U) =>
      Real.exp
        ((∑ i : Fin m,
            (c i)⁻¹ * inner ℝ (e i) (m_nu - m_mu) * inner ℝ (e i) (u - m_mu))
          - (∑ i : Fin m, (c i)⁻¹ * (inner ℝ (e i) (m_nu - m_mu)) ^ 2) / 2)
    let f : U → ℝ := fun u : U =>
      Real.exp
        ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
          - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2)
    have hKbound : ∀ m : ℕ,
        (∫⁻ u : U, ENNReal.ofReal ((F m u) ^ 2) ∂mu)
          ≤ ENNReal.ofReal
              (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2)) := by
      intro m
      rw [lintegral_congr (fun u : U => ENNReal.ofReal_pow (le_of_lt (Real.exp_pos _)) 2)]
      rw [hL2mu_gen m]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le ?_)
      rw [hrange2 m]
      exact Summable.sum_le_tsum (Finset.range m)
        (fun i _ => mul_nonneg (le_of_lt (inv_pos.mpr (hc_pos i))) (sq_nonneg _)) hsigma2
    have hlim : ∀ᶠ m in Filter.atTop,
        (∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
            ENNReal.ofReal (F m u) ∂mu)
          = nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C) :=
      Filter.eventually_atTop.2 ⟨n, fun m hm => (hstep3 n m hm C hC).symm⟩
    exact (hstep3 n n le_rfl C hC).symm.trans
      ((statopia_math_node_1214593279_6b91f964 U mu
        ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C) hA
        F hdens_real_meas (fun m u => (Real.exp_pos _).le)
        f (fun u => (Real.exp_pos _).le) hconv_fin
        (Real.exp (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2))
        hKbound
        (nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C))
        (measure_ne_top nu _) hlim).symm)
  have key : nu ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C)
      = ∫⁻ u in ((fun u : U => fun i : Fin n => inner ℝ (e i) u) ⁻¹' C),
          ENNReal.ofReal
            (Real.exp
              ((∑' k : ℕ, (c k)⁻¹ * inner ℝ (e k) (m_nu - m_mu) * inner ℝ (e k) (u - m_mu))
                - (∑' k : ℕ, (c k)⁻¹ * (inner ℝ (e k) (m_nu - m_mu)) ^ 2) / 2)) ∂mu :=
    (hcyl n C hC).trans (hlint1.trans hlint2)
  rw [MeasureTheory.withDensity_apply _ hA]
  exact key
  /- @proof-region region.target-node.session.3b0afdebe8f1acdc end -/

end Statlib.Imported
end

