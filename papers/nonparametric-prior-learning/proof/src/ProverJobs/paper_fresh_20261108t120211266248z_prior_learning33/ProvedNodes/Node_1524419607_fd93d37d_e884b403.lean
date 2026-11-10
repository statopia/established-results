import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_1524419607_fd93d37d : ∀ (E : Type*) [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℝ) (hZ : 0 < Z)
    (Zn : ℕ → ℝ) (hZn : ∀ n : ℕ, 0 < Zn n)
    (hZn_tendsto : Tendsto (fun n : ℕ => (Real.sqrt (Zn n))⁻¹) atTop (𝓝 ((Real.sqrt Z)⁻¹)))
    (hZn_large : ∀ᶠ n : ℕ in atTop, Z / 2 < Zn n)
    (rho : ℕ → E → ℝ≥0∞) (hrho : ∀ n : ℕ, Measurable (rho n))
    (f : E → ℝ) (fn : ℕ → E → ℝ)
    (hf_nonneg : ∀ u : E, 0 ≤ f u)
    (hfn_nonneg : ∀ (n : ℕ) (u : E), 0 ≤ fn n u)
    (hf_meas : AEMeasurable f P)
    (hfn_meas : ∀ n : ℕ, AEMeasurable (fn n) P)
    (h1 : ∫⁻ u : E, ENNReal.ofReal (f u) ∂P = ENNReal.ofReal Z)
    (h2 : Tendsto
      (fun n : ℕ => ∫⁻ u : E,
        ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂P)
      atTop (𝓝 0))
    (h3 : Tendsto
      (fun n : ℕ => ∫⁻ u : E,
        rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2) ∂P)
      atTop (𝓝 0)),
    Tendsto
      (fun n : ℕ => Real.sqrt ((1 / 2 : ℝ) *
        (∫⁻ u : E, ENNReal.ofReal ((((Real.sqrt Z))⁻¹ * Real.sqrt (f u) -
          Real.sqrt ((rho n u).toReal) * (((Real.sqrt (Zn n))⁻¹) * Real.sqrt (fn n u))) ^ 2) ∂P).toReal))
      atTop (𝓝 0) := by
  /- @proof-region region.target-node.session.98355bfc476b7bd3 begin -/
  intro E _ P _ Z hZ Zn hZn hZn_tendsto hZn_large rho hrho f fn hf_nonneg hfn_nonneg hf_meas hfn_meas h1 h2 h3
  have hspos : 0 < Real.sqrt Z := Real.sqrt_pos.mpr hZ
  have hcpos : 0 < (Real.sqrt Z)⁻¹ := inv_pos.mpr hspos
  have ha_sq : ∀ u : E, Real.sqrt (f u) ^ 2 = f u := fun u => Real.sq_sqrt (hf_nonneg u)
  have han_sq : ∀ (n : ℕ) (u : E), Real.sqrt (fn n u) ^ 2 = fn n u :=
    fun n u => Real.sq_sqrt (hfn_nonneg n u)
  have hr_sq : ∀ (n : ℕ) (u : E), Real.sqrt ((rho n u).toReal) ^ 2 = (rho n u).toReal :=
    fun n u => Real.sq_sqrt ENNReal.toReal_nonneg
  have hr_meas : ∀ n : ℕ, Measurable fun u : E => (rho n u).toReal :=
    fun n => ENNReal.measurable_toReal.comp (hrho n)
  have hr_sqrt_meas : ∀ n : ℕ, Measurable fun u : E => Real.sqrt ((rho n u).toReal) :=
    fun n => Real.continuous_sqrt.measurable.comp (hr_meas n)
  have hq_meas : ∀ n : ℕ, Measurable fun u : E => (Real.sqrt ((rho n u).toReal) - 1) ^ 2 := by
    intro n
    have hq1 : Measurable fun u : E => Real.sqrt ((rho n u).toReal) + (-1) :=
      (hr_sqrt_meas n).add measurable_const
    have hq2 : Measurable fun u : E =>
        (Real.sqrt ((rho n u).toReal) + (-1)) * (Real.sqrt ((rho n u).toReal) + (-1)) := hq1.mul hq1
    simpa [sub_eq_add_neg, pow_two] using hq2
  have hF_meas : ∀ n : ℕ,
      AEMeasurable (fun u : E => ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)) P :=
    fun n => (hf_meas.mul (hq_meas n).aemeasurable).ennreal_ofReal
  have hf_meas' : AEMeasurable (fun u : E => ENNReal.ofReal (f u)) P := hf_meas.ennreal_ofReal
  have ha_meas : AEMeasurable (fun u : E => Real.sqrt (f u)) P := hf_meas.sqrt
  have han_meas : ∀ n : ℕ, AEMeasurable (fun u : E => Real.sqrt (fn n u)) P :=
    fun n => (hfn_meas n).sqrt
  have hG_meas : ∀ n : ℕ, AEMeasurable
      (fun u : E => rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2)) P := by
    intro n
    have hd : AEMeasurable (fun u : E => Real.sqrt (fn n u) - Real.sqrt (f u)) P :=
      (han_meas n).sub ha_meas
    have hd2 : AEMeasurable (fun u : E => (Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2) P := by
      simpa [pow_two] using hd.mul hd
    exact (hrho n).aemeasurable.mul hd2.ennreal_ofReal
  have hI : Tendsto (fun n : ℕ => (∫⁻ u : E, ENNReal.ofReal ((((Real.sqrt Z))⁻¹ * Real.sqrt (f u) -
      Real.sqrt ((rho n u).toReal) * (((Real.sqrt (Zn n))⁻¹) * Real.sqrt (fn n u))) ^ 2) ∂P).toReal) atTop (𝓝 0) := by
    have hsa : ∀ u : E, Real.sqrt (f u) ^ 2 = f u := fun u => Real.sq_sqrt (hf_nonneg u)
    have hkey : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 4 * x ^ 2 + 4 * y ^ 2 + 2 * z ^ 2 := by
      intro x y z
      nlinarith [sq_nonneg (x - y), sq_nonneg (z - x - y)]
    have hpt : ∀ (n : ℕ) (u : E),
        ((Real.sqrt Z)⁻¹ * Real.sqrt (f u) - Real.sqrt ((rho n u).toReal) *
          ((Real.sqrt (Zn n))⁻¹ * Real.sqrt (fn n u))) ^ 2
        ≤ 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
          + 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 *
              ((Real.sqrt ((rho n u).toReal)) ^ 2 *
                (Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2)
          + 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * f u := by
      intro n u
      have hid : (Real.sqrt Z)⁻¹ * Real.sqrt (f u) - Real.sqrt ((rho n u).toReal) *
          ((Real.sqrt (Zn n))⁻¹ * Real.sqrt (fn n u))
          = (Real.sqrt (Zn n))⁻¹ * (Real.sqrt (f u) * (1 - Real.sqrt ((rho n u).toReal)))
            + (Real.sqrt (Zn n))⁻¹ *
                (Real.sqrt ((rho n u).toReal) * (Real.sqrt (f u) - Real.sqrt (fn n u)))
            + ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) * Real.sqrt (f u) := by ring
      have hK := hkey
        ((Real.sqrt (Zn n))⁻¹ * (Real.sqrt (f u) * (1 - Real.sqrt ((rho n u).toReal))))
        ((Real.sqrt (Zn n))⁻¹ *
          (Real.sqrt ((rho n u).toReal) * (Real.sqrt (f u) - Real.sqrt (fn n u))))
        (((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) * Real.sqrt (f u))
      have hX : 4 * ((Real.sqrt (Zn n))⁻¹ *
            (Real.sqrt (f u) * (1 - Real.sqrt ((rho n u).toReal)))) ^ 2
          = 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) := by
        calc 4 * ((Real.sqrt (Zn n))⁻¹ *
              (Real.sqrt (f u) * (1 - Real.sqrt ((rho n u).toReal)))) ^ 2
            = 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 *
                (Real.sqrt (f u) ^ 2 * (1 - Real.sqrt ((rho n u).toReal)) ^ 2) := by ring
          _ = 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) := by
              rw [hsa u]; ring
      have hY : 4 * ((Real.sqrt (Zn n))⁻¹ *
            (Real.sqrt ((rho n u).toReal) * (Real.sqrt (f u) - Real.sqrt (fn n u)))) ^ 2
          = 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 *
              ((Real.sqrt ((rho n u).toReal)) ^ 2 *
                (Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2) := by ring
      have hZ : 2 * (((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) * Real.sqrt (f u)) ^ 2
          = 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * f u := by
        calc 2 * (((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) * Real.sqrt (f u)) ^ 2
            = 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Real.sqrt (f u) ^ 2 := by ring
          _ = 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * f u := by rw [hsa u]
      rw [hid]
      rw [hX, hY, hZ] at hK
      exact hK
    set A : ℕ → ℝ≥0∞ := fun n => ∫⁻ u : E,
      ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂P with hAdef
    set B : ℕ → ℝ≥0∞ := fun n => ∫⁻ u : E,
      rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2) ∂P with hBdef
    set I : ℕ → ℝ≥0∞ := fun n => ∫⁻ u : E,
      ENNReal.ofReal ((((Real.sqrt Z))⁻¹ * Real.sqrt (f u) -
        Real.sqrt ((rho n u).toReal) * (((Real.sqrt (Zn n))⁻¹) * Real.sqrt (fn n u))) ^ 2) ∂P with hIdef
    have h2A : Tendsto A atTop (𝓝 0) := by simpa only [hAdef] using h2
    have h3B : Tendsto B atTop (𝓝 0) := by simpa only [hBdef] using h3
    have hA0 : Tendsto (fun n : ℕ => (A n).toReal) atTop (𝓝 0) := by
      rw [tendsto_order]
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · filter_upwards with n
        exact lt_of_lt_of_le hb ENNReal.toReal_nonneg
      · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal b := ENNReal.ofReal_pos.mpr hb
        filter_upwards [h2A.eventually (Iio_mem_nhds hpos)] with n hn
        exact ENNReal.toReal_lt_of_lt_ofReal hn
    have hB0 : Tendsto (fun n : ℕ => (B n).toReal) atTop (𝓝 0) := by
      rw [tendsto_order]
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · filter_upwards with n
        exact lt_of_lt_of_le hb ENNReal.toReal_nonneg
      · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal b := ENNReal.ofReal_pos.mpr hb
        filter_upwards [h3B.eventually (Iio_mem_nhds hpos)] with n hn
        exact ENNReal.toReal_lt_of_lt_ofReal hn
    have hmul : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        ENNReal.ofReal (a * b) = ENNReal.ofReal a * ENNReal.ofReal b :=
      fun a b ha _ => ENNReal.ofReal_mul ha
    have hadd3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
        ENNReal.ofReal (a + b + c) =
          ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c := by
      intro a b c ha hb hc
      rw [ENNReal.ofReal_add (add_nonneg ha hb) hc, ENNReal.ofReal_add ha hb]
    have hptE : ∀ (n : ℕ) (u : E),
        ENNReal.ofReal ((((Real.sqrt Z))⁻¹ * Real.sqrt (f u) -
          Real.sqrt ((rho n u).toReal) * (((Real.sqrt (Zn n))⁻¹) * Real.sqrt (fn n u))) ^ 2)
        ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
            ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
          + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
              (rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2))
          + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
              ENNReal.ofReal (f u) := by
      intro n u
      have hn1 : (0:ℝ) ≤ f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2 :=
        mul_nonneg (hf_nonneg u) (sq_nonneg _)
      have hn2 : (0:ℝ) ≤ (Real.sqrt ((rho n u).toReal)) ^ 2 *
          (Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hn3 : (0:ℝ) ≤ f u := hf_nonneg u
      have hK1 : (0:ℝ) ≤ 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
      have hK2 : (0:ℝ) ≤ 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      have hsum : ENNReal.ofReal
            (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
              + 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 *
                  ((Real.sqrt ((rho n u).toReal)) ^ 2 *
                    (Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2)
              + 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * f u)
          = ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
              ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
            + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
                ENNReal.ofReal ((Real.sqrt ((rho n u).toReal)) ^ 2 *
                  (Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2)
            + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
                ENNReal.ofReal (f u) := by
        rw [hadd3 _ _ _ (mul_nonneg hK1 hn1) (mul_nonneg hK1 hn2) (mul_nonneg hK2 hn3),
          hmul _ _ hK1 hn1, hmul _ _ hK1 hn2, hmul _ _ hK2 hn3]
      have hbase := ENNReal.ofReal_le_ofReal (hpt n u)
      have hcore : ENNReal.ofReal ((Real.sqrt ((rho n u).toReal)) ^ 2 *
            (Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2)
          ≤ rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2) := by
        have harg : (Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2 =
            (Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2 := by ring
        rw [harg, hmul ((Real.sqrt ((rho n u).toReal)) ^ 2)
            ((Real.sqrt (f u) - Real.sqrt (fn n u)) ^ 2) (sq_nonneg _) (sq_nonneg _), hr_sq n u]
        exact mul_le_mul_of_nonneg_right ENNReal.ofReal_toReal_le bot_le
      rw [hsum] at hbase
      exact hbase.trans
        (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcore bot_le)) le_rfl)
    have hIle : ∀ n : ℕ, I n ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * A n
          + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * B n
          + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
              ENNReal.ofReal Z := by
      intro n
      have m1 : AEMeasurable (fun u : E => ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
          ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)) P :=
        measurable_const.aemeasurable.mul (hF_meas n)
      have m2 : AEMeasurable (fun u : E => ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
          (rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2))) P :=
        measurable_const.aemeasurable.mul (hG_meas n)
      have e1 : ∫⁻ u : E, ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
            ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2) ∂P
          = ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * A n := by
        rw [lintegral_const_mul'' _ (hF_meas n), hAdef]
      have e2 : ∫⁻ u : E, ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
            (rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2)) ∂P
          = ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * B n := by
        rw [lintegral_const_mul'' _ (hG_meas n), hBdef]
      have e3 : ∫⁻ u : E, ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
            ENNReal.ofReal (f u) ∂P
          = ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
              ENNReal.ofReal Z := by
        rw [lintegral_const_mul'' _ hf_meas', h1]
      calc I n
          ≤ ∫⁻ u : E, (ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
                  ENNReal.ofReal (f u * (Real.sqrt ((rho n u).toReal) - 1) ^ 2)
                + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
                    (rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2))
                + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
                    ENNReal.ofReal (f u)) ∂P := by
              rw [hIdef]
              exact lintegral_mono (hptE n)
        _ = ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * A n
              + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * B n
              + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
                  ENNReal.ofReal Z := by
              rw [lintegral_add_left' (m1.add m2) (fun u : E =>
                    ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
                      ENNReal.ofReal (f u)),
                  lintegral_add_left' m1 (fun u : E =>
                    ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
                      (rho n u * ENNReal.ofReal ((Real.sqrt (fn n u) - Real.sqrt (f u)) ^ 2))),
                  e1, e2, e3]
    have hfin : ∀ᶠ n : ℕ in atTop, A n ≠ ⊤ := by
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal 1 := ENNReal.ofReal_pos.mpr one_pos
      filter_upwards [h2A.eventually (Iio_mem_nhds hpos)] with n hn
      exact (lt_of_lt_of_le hn le_top).ne
    have hbfin : ∀ᶠ n : ℕ in atTop, B n ≠ ⊤ := by
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal 1 := ENNReal.ofReal_pos.mpr one_pos
      filter_upwards [h3B.eventually (Iio_mem_nhds hpos)] with n hn
      exact (lt_of_lt_of_le hn le_top).ne
    have hbound : ∀ᶠ n : ℕ in atTop, (I n).toReal ≤
        4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal
          + 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal
          + 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z := by
      filter_upwards [hfin, hbfin] with n hAn hBn
      have hK1 : (0:ℝ) ≤ 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
      have hK2 : (0:ℝ) ≤ 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      have hofA : ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * A n
          ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal) := by
        calc ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * A n
            ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
                ENNReal.ofReal (A n).toReal :=
              mul_le_mul_of_nonneg_left (le_of_eq (ENNReal.ofReal_toReal hAn).symm) bot_le
          _ = ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal) :=
              (hmul _ _ hK1 ENNReal.toReal_nonneg).symm
      have hofB : ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * B n
          ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal) := by
        calc ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * B n
            ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) *
                ENNReal.ofReal (B n).toReal :=
              mul_le_mul_of_nonneg_left (le_of_eq (ENNReal.ofReal_toReal hBn).symm) bot_le
          _ = ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal) :=
              (hmul _ _ hK1 ENNReal.toReal_nonneg).symm
      have hofZ : ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
            ENNReal.ofReal Z
          = ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z) :=
        (hmul _ _ hK2 (le_of_lt hZ)).symm
      have hstep : I n ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal)
          + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal)
          + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z) := by
        calc I n ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * A n
              + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) * B n
              + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) *
                  ENNReal.ofReal Z := hIle n
          _ ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal)
              + ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal)
              + ENNReal.ofReal (2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z) := by
              rw [hofZ]
              exact add_le_add (add_le_add hofA hofB) le_rfl
      have hr : (0:ℝ) ≤ 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal
          + 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal
          + 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z :=
        add_nonneg (add_nonneg (mul_nonneg hK1 ENNReal.toReal_nonneg)
          (mul_nonneg hK1 ENNReal.toReal_nonneg)) (mul_nonneg hK2 (le_of_lt hZ))
      have hs : I n ≤ ENNReal.ofReal (4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal
          + 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal
          + 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z) := by
        rw [hadd3 _ _ _ (mul_nonneg hK1 ENNReal.toReal_nonneg)
          (mul_nonneg hK1 ENNReal.toReal_nonneg) (mul_nonneg hK2 (le_of_lt hZ))]
        exact hstep
      exact ENNReal.toReal_le_of_le_ofReal hr hs
    have hupper : Tendsto (fun n : ℕ => 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal
        + 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal
        + 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z) atTop (𝓝 0) := by
      have hd2 : Tendsto (fun n : ℕ => ((Real.sqrt (Zn n))⁻¹) ^ 2) atTop
          (𝓝 (((Real.sqrt Z)⁻¹) ^ 2)) := by
        simpa [pow_two] using hZn_tendsto.mul hZn_tendsto
      have hk : Tendsto (fun n : ℕ => 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2) atTop
          (𝓝 (4 * ((Real.sqrt Z)⁻¹) ^ 2)) := hd2.const_mul 4
      have hp1 : Tendsto (fun n : ℕ => 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (A n).toReal)
          atTop (𝓝 0) := by
        simpa using hk.mul hA0
      have hp2 : Tendsto (fun n : ℕ => 4 * ((Real.sqrt (Zn n))⁻¹) ^ 2 * (B n).toReal)
          atTop (𝓝 0) := by
        simpa using hk.mul hB0
      have hsub : Tendsto (fun n : ℕ => (Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) atTop
          (𝓝 ((Real.sqrt Z)⁻¹ - (Real.sqrt Z)⁻¹)) := by
        have h := hZn_tendsto.neg.const_add ((Real.sqrt Z)⁻¹)
        simpa [sub_eq_add_neg] using h
      have hsq : Tendsto (fun n : ℕ => ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2) atTop
          (𝓝 (((Real.sqrt Z)⁻¹ - (Real.sqrt Z)⁻¹) ^ 2)) := by
        simpa [pow_two] using hsub.mul hsub
      have hp3 : Tendsto (fun n : ℕ => 2 * ((Real.sqrt Z)⁻¹ - (Real.sqrt (Zn n))⁻¹) ^ 2 * Z)
          atTop (𝓝 0) := by
        have h := (hsq.mul_const Z).const_mul 2
        simpa [mul_assoc, mul_comm, mul_left_comm] using h
      simpa using (hp1.add hp2).add hp3
    have hI0 : Tendsto (fun n : ℕ => (I n).toReal) atTop (𝓝 0) := by
      rw [tendsto_order]
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · filter_upwards with n
        exact lt_of_lt_of_le hb ENNReal.toReal_nonneg
      · filter_upwards [hbound, hupper.eventually (Iio_mem_nhds hb)] with n hle hlt
        exact lt_of_le_of_lt hle hlt
    simpa only [hIdef] using hI0
  have h2' : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (∫⁻ u : E, ENNReal.ofReal ((((Real.sqrt Z))⁻¹ * Real.sqrt (f u) -
      Real.sqrt ((rho n u).toReal) * (((Real.sqrt (Zn n))⁻¹) * Real.sqrt (fn n u))) ^ 2) ∂P).toReal) atTop (𝓝 0) := by
    simpa using hI.const_mul (1 / 2 : ℝ)
  have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h2'
  rw [Real.sqrt_zero] at hcomp
  exact hcomp
  /- @proof-region region.target-node.session.98355bfc476b7bd3 end -/

end Statlib.Imported
end

