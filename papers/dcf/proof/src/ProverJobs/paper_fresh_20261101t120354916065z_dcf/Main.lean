import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.RandomVariable.Gaussian.Standard
import Lean
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ExternalNodes.Node_014c7ace551946d99df2
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ExternalNodes.Node_3feff6b2c2d242ce9504
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Vocabulary
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.ProvedNodes
import ProverJobs.paper_fresh_20261101t120354916065z_dcf.Base

namespace PaperProofTasks.paper_fresh_20261101t120354916065z_dcf
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

theorem Theorem_1_two_sample_Gaussian_approximation_over_rectangles_rho_n_m_double_star_bound_uniform_variance :
    ∀ (δ1 δ2 b : ℝ), 0 < δ2 → δ2 < δ1 → 0 < b →
      ∃ K3 : ℝ, 0 < K3 ∧ ∃ c1 : ℝ, 0 < c1 ∧
        ∀ (δ : ℕ → ℕ → ℝ),
          (∀ (n m : ℕ), 0 < n → 0 < m → δ2 < |δ n m| ∧ |δ n m| < δ1) →
          ∀ (n : ℕ), 0 < n → ∀ (m : ℕ), 0 < m → ∀ (p : ℕ), 2 ≤ p →
            ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (μX μY : Fin p → ℝ)
              (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
              (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ),
              (∀ i, Measurable (X i)) →
              (∀ i, Measurable (Y i)) →
              (∀ i, Measurable (F i)) →
              (∀ i, Measurable (G i)) →
              iIndepFun (fun i => jointFamily X Y F G i) P →
              (∀ i j, Integrable (fun ω => X i ω j) P) →
              (∀ i j, ∫ ω, X i ω j ∂P = μX j) →
              (∀ i j, Integrable (fun ω => Y i ω j) P) →
              (∀ i j, ∫ ω, Y i ω j ∂P = μY j) →
              (∀ i j k, Integrable (fun ω => (X i ω j - μX j) * (X i ω k - μX k)) P) →
              (∀ i j k, Integrable (fun ω => (Y i ω j - μY j) * (Y i ω k - μY k)) P) →
              (∀ i j, Integrable (fun ω => |X i ω j - μX j| ^ 3) P) →
              (∀ i j, Integrable (fun ω => |Y i ω j - μY j| ^ 3) P) →
              (∀ i, IsCenteredGaussianVector P (fun ω j => F i ω j - μX j)
                (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)) →
              (∀ i, IsCenteredGaussianVector P (fun ω j => G i ω j - μY j)
                (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)) →
              (∀ j, Integrable
                (fun ω => (combinedStat n m (δ n m) μX μY X Y ω j) ^ 2) P) →
              (∀ j, b ≤ ∫ ω, (combinedStat n m (δ n m) μX μY X Y ω j) ^ 2 ∂P) →
                          ∀ (B : ℝ), 1 ≤ B →
                            LThird P X μX ≤ B →
                            LThird P Y μY ≤ B →
                            (∀ i j, Integrable (fun ω => Real.exp (|X i ω j - μX j| / B)) P) →
                            (∀ i j, ∫ ω, Real.exp (|X i ω j - μX j| / B) ∂P ≤ 2) →
                            (∀ i j, Integrable (fun ω => Real.exp (|Y i ω j - μY j| / B)) P) →
                            (∀ i j, ∫ ω, Real.exp (|Y i ω j - μY j| / B) ∂P ≤ 2) →
                            B ^ 2 * (Real.log ((p : ℝ) * (n : ℝ))) ^ 7 / (n : ℝ) ≤ c1 →
                            B ^ 2 * (Real.log ((p : ℝ) * (m : ℝ))) ^ 7 / (m : ℝ) ≤ c1 →
                            rhoStarStar P (combinedStat n m (δ n m) μX μY X Y)
                                (combinedStat n m (δ n m) μX μY F G)
                              ≤ K3 * ((B ^ 2 * (Real.log ((p : ℝ) * (n : ℝ))) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6)
                                  + (B ^ 2 * (Real.log ((p : ℝ) * (m : ℝ))) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6))
:= by
  /- @proof-region region.root.38d5f2c27e39 begin -/
  intro δ1 δ2 b hδ2 hδ21 hb
  have hδ1 : 0 < δ1 := lt_trans hδ2 hδ21
  set Cvar : ℝ := sSup {y : ℝ | ∃ x : ℝ, 0 < x ∧ y = x ^ 2 / (Real.exp x - 1)} with hCvar
  obtain ⟨hCvar_pos, hCvar_lt, -, -⟩ :=
    statopia_math_node_3453903389_21203619 (Ω := Unit) (P := Measure.dirac ()) 1 Cvar one_pos
      hCvar (fun _ => (0 : ℝ)) measurable_const (by simp) (by simp)
  obtain ⟨Kstar2, hKstar2_pos, K1e, hK1e_pos, hK1e_le, K2, hK2_pos, hL4⟩ :=
    PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.paper_2d165b9668ee43088292ee6f2129e2cd.{0}
      b hb
  obtain ⟨c1, hc1_pos, K1, hK1_pos, hc1_le, hK1_le, hK1_eq, hK1_c13, hK1_sq, hthresh⟩ :=
    statopia_math_node_2877967487_e4e3f4f7 δ1 Cvar (1 + K1e⁻¹) hδ1 hCvar_pos hCvar_lt
      (add_pos one_pos (inv_pos.mpr hK1e_pos))
  have hK1e_le_half : K1e ≤ 1 / 2 := by
    have h2 : (max Kstar2 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (le_max_right Kstar2 (2 : ℝ))
    calc K1e ≤ (max Kstar2 2)⁻¹ := hK1e_le
      _ ≤ (2 : ℝ)⁻¹ := h2
      _ = 1 / 2 := by norm_num
  
  have hK1_le_K1e : K1 ≤ K1e := by
    have h1 : (1 : ℝ) ≤ K1e⁻¹ := by
      rw [← one_div, one_le_div_iff]
      exact Or.inl ⟨hK1e_pos, by linarith⟩
    have hmaxeq : max (1 + K1e⁻¹) 2 = 1 + K1e⁻¹ := max_eq_left (by linarith)
    rw [hmaxeq] at hK1_le
    have hpos : (0 : ℝ) < 1 + K1e⁻¹ := by linarith
    have h2 : (1 + K1e⁻¹)⁻¹ ≤ K1e := by
      rw [← one_div, div_le_iff₀ hpos]
      have h3 : K1e * (1 + K1e⁻¹) = K1e + 1 := by
        field_simp
      linarith
    linarith
  let kap : ℝ := K1e / K1
  let CM : ℝ := 32 * (1 / (8 * Real.log 2) + Real.log 2 ^ ((-7 : ℝ) / 2)) ^ 3
  have hkap : 0 < kap := div_pos hK1e_pos hK1_pos
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcl : 0 < Real.log 2 ^ ((-7 : ℝ) / 6) := Real.rpow_pos_of_pos hl2 _
  have hCM : 0 < CM := by
    have h1 : (0 : ℝ) < 1 / (8 * Real.log 2) := div_pos one_pos (mul_pos (by norm_num) hl2)
    have h2 : (0 : ℝ) < Real.log 2 ^ ((-7 : ℝ) / 2) := Real.rpow_pos_of_pos hl2 _
    exact mul_pos (by norm_num) (pow_pos (add_pos h1 h2) 3)
  have hK3pos :
      0 < K2 * max (kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6))
          (δ1 * kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) + 1 := by
    have h1 : 0 < CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6) :=
      mul_pos (div_pos hCM (pow_pos hkap 3)) hcl
    have h2 : 0 < max (kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6))
        (δ1 * kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    linarith [mul_pos hK2_pos h2]
  refine ⟨K2 * max (kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6))
        (δ1 * kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) + 1, hK3pos, c1,
      hc1_pos, ?_⟩
  intro δ hδ n hn m hm p hp Ω inst P instP μX μY X Y F G hXm hYm hFm hGm hind hXi hXμ hYi hYμ
    hX2 hY2 hX3 hY3 hFg hGg hcombI hbv B hB hLX hLY hXeI hXe hYeI hYe hcn hcm
  obtain ⟨hφn_ge, hφm_ge, htn_C, htm_C, htn_D, htm_D, htn_E, htm_E⟩ :=
    hthresh n hn m hm p hp B hB (δ n m) (lt_trans hδ2 (hδ n m hn hm).1) (hδ n m hn hm).2 hcn hcm
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB
  let xiX : Fin n → Ω → ℝ := fun i ω => ⨆ j : Fin p, |X i ω j - μX j|
  have hxiX : ∀ i : Fin n, Measurable (xiX i) ∧ (∀ ω : Ω, 0 ≤ xiX i ω) ∧
      ∀ s : ℝ, 0 ≤ s → (P {ω : Ω | xiX i ω > s}).toReal ≤ 2 * (p : ℝ) * Real.exp (-s / B) := by
    intro i
    have hraw := statopia_math_node_3839919428_91a7f533 (Ω := Ω) (P := P) p (by omega) B hBpos μX
      (fun (j : Fin p) ω => X i ω j) (xiX i) (fun j => (measurable_pi_apply j).comp (hXm i))
      (fun ω => rfl) (fun j => hXeI i j) (fun j => hXe i j)
    refine ⟨hraw.1, hraw.2.1, fun s hs => ?_⟩
    have hne : ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-s / B)) ≠ ⊤ :=
      ne_of_lt ENNReal.ofReal_lt_top
    exact le_trans (ENNReal.toReal_mono hne (hraw.2.2 s hs))
      (le_of_eq (ENNReal.toReal_ofReal (by positivity)))
  let xiY : Fin m → Ω → ℝ := fun i ω => ⨆ j : Fin p, |Y i ω j - μY j|
  have hxiY : ∀ i : Fin m, Measurable (xiY i) ∧ (∀ ω : Ω, 0 ≤ xiY i ω) ∧
      ∀ s : ℝ, 0 ≤ s → (P {ω : Ω | xiY i ω > s}).toReal ≤ 2 * (p : ℝ) * Real.exp (-s / B) := by
    intro i
    have hraw := statopia_math_node_3839919428_91a7f533 (Ω := Ω) (P := P) p (by omega) B hBpos μY
      (fun (j : Fin p) ω => Y i ω j) (xiY i) (fun j => (measurable_pi_apply j).comp (hYm i))
      (fun ω => rfl) (fun j => hYeI i j) (fun j => hYe i j)
    refine ⟨hraw.1, hraw.2.1, fun s hs => ?_⟩
    have hne : ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-s / B)) ≠ ⊤ :=
      ne_of_lt ENNReal.ofReal_lt_top
    exact le_trans (ENNReal.toReal_mono hne (hraw.2.2 s hs))
      (le_of_eq (ENNReal.toReal_ofReal (by positivity)))
  have hp2 : (1 : ℝ) < (p : ℝ) := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp2
  let xiF : Fin n → Ω → ℝ := fun i ω => ⨆ j : Fin p, |F i ω j - μX j|
  have hxiF : ∀ i : Fin n, Measurable (xiF i) ∧ (∀ ω : Ω, 0 ≤ xiF i ω) ∧
      ∀ s : ℝ, 0 ≤ s → (P {ω : Ω | xiF i ω > s}).toReal ≤
        2 * (p : ℝ) * Real.exp (-(s ^ 2) / (2 * Cvar * B ^ 2)) := by
    intro i
    have hfm : ∀ j : Fin p, Measurable fun ω => F i ω j - μX j :=
      fun j => ((measurable_pi_apply j).comp (hFm i)).sub measurable_const
    have hsymm : ∀ j k : Fin p,
        (∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
          = ∫ ω, (X i ω k - μX k) * (X i ω j - μX j) ∂P := by
      intro j k
      simp only [mul_comm]
    have hPSD :
        Matrix.PosSemidef (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P) := by
      have h0 := (hFg i).posSemidef_symmetrizedCovariance (p := p) (by omega : 1 ≤ p)
      have h0' :
          ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
            + Matrix.transpose
                (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)))).PosSemidef :=
        h0
      have heq :
          ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
            + Matrix.transpose
                (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P))))
            = Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P) := by
        ext j k
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
          smul_eq_mul]
        rw [← hsymm j k]
        ring
      rw [heq] at h0'
      exact h0'
    have hlaw : ∀ j : Fin p,
        Measure.map (fun ω => F i ω j - μX j) P
          = gaussianReal 0 ⟨∫ ω, (X i ω j - μX j) * (X i ω j - μX j) ∂P,
              integral_nonneg (fun ω => mul_self_nonneg (X i ω j - μX j))⟩ := by
      intro j
      set u : Fin p → ℝ := fun a => if a = j then (1 : ℝ) else 0 with hu
      have hzero : ∀ b : Fin p, b ≠ j → u b = 0 := by
        intro b hb
        simp [hu, hb]
      have hone : u j = 1 := by
        simp [hu]
      have hfun : (fun ω => ∑ a : Fin p, u a * (F i ω a - μX a))
          = fun ω => F i ω j - μX j := by
        funext ω
        rw [Finset.sum_eq_single j]
        · rw [hone]; ring
        · intro b _ hb; rw [hzero b hb]; ring
        · intro h; exact absurd (Finset.mem_univ j) h
      have hquad : (∑ a : Fin p, ∑ b : Fin p,
            u a * (∫ ω, (X i ω a - μX a) * (X i ω b - μX b) ∂P) * u b)
          = ∫ ω, (X i ω j - μX j) * (X i ω j - μX j) ∂P := by
        rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single j]
          · rw [hone]; ring
          · intro b _ hb; rw [hzero b hb]; ring
          · intro h; exact absurd (Finset.mem_univ j) h
        · intro a _ ha
          rw [hzero a ha]
          simp
        · intro h; exact absurd (Finset.mem_univ j) h
      have h := IsCenteredGaussianVector.map_linearCombination P (fun ω a => F i ω a - μX a)
        (fun a b => ∫ ω, (X i ω a - μX a) * (X i ω b - μX b) ∂P) (hFg i) hPSD u
      rw [← hfun, h]
      exact congrArg (fun v : NNReal => gaussianReal (0 : ℝ) v) (Subtype.ext hquad)
    have hsigma_le : ∀ j : Fin p,
        (∫ ω, (X i ω j - μX j) * (X i ω j - μX j) ∂P) ≤ Cvar * B ^ 2 := by
      intro j
      have h := (statopia_math_node_3453903389_21203619 (Ω := Ω) (P := P) B Cvar hBpos hCvar
        (fun ω => X i ω j - μX j)
        (((measurable_pi_apply j).comp (hXm i)).sub measurable_const) (hXeI i j) (hXe i j)).2.2.2
      simpa [pow_two] using h
    have hraw := statopia_math_node_1099282424_527c2f42 (Ω := Ω) (P := P) p (by omega)
      (Cvar * B ^ 2) (by positivity) (fun (j : Fin p) ω => F i ω j - μX j) hfm
      (fun j => ∫ ω, (X i ω j - μX j) * (X i ω j - μX j) ∂P)
      (fun j => integral_nonneg (fun ω => mul_self_nonneg (X i ω j - μX j))) hsigma_le hlaw
    refine ⟨hraw.1, hraw.2.1, fun s hs => ?_⟩
    have harg : -(s ^ 2) / (2 * (Cvar * B ^ 2)) = -(s ^ 2) / (2 * Cvar * B ^ 2) := by
      rw [← mul_assoc]
    have hne : ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-(s ^ 2) / (2 * (Cvar * B ^ 2)))) ≠ ⊤ :=
      ne_of_lt ENNReal.ofReal_lt_top
    have hstep := ENNReal.toReal_mono hne (hraw.2.2 s hs)
    rw [ENNReal.toReal_ofReal (by positivity), harg] at hstep
    exact hstep
  let xiG : Fin m → Ω → ℝ := fun i ω => ⨆ j : Fin p, |G i ω j - μY j|
  have hxiG : ∀ i : Fin m, Measurable (xiG i) ∧ (∀ ω : Ω, 0 ≤ xiG i ω) ∧
      ∀ s : ℝ, 0 ≤ s → (P {ω : Ω | xiG i ω > s}).toReal ≤
        2 * (p : ℝ) * Real.exp (-(s ^ 2) / (2 * Cvar * B ^ 2)) := by
    intro i
    have hgm : ∀ j : Fin p, Measurable fun ω => G i ω j - μY j :=
      fun j => ((measurable_pi_apply j).comp (hGm i)).sub measurable_const
    have hsymm : ∀ j k : Fin p,
        (∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
          = ∫ ω, (Y i ω k - μY k) * (Y i ω j - μY j) ∂P := by
      intro j k
      simp only [mul_comm]
    have hPSD :
        Matrix.PosSemidef (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P) := by
      have h0 := (hGg i).posSemidef_symmetrizedCovariance (p := p) (by omega : 1 ≤ p)
      have h0' :
          ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
            + Matrix.transpose
                (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)))).PosSemidef :=
        h0
      have heq :
          ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
            + Matrix.transpose
                (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P))))
            = Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P) := by
        ext j k
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
          smul_eq_mul]
        rw [← hsymm j k]
        ring
      rw [heq] at h0'
      exact h0'
    have hlaw : ∀ j : Fin p,
        Measure.map (fun ω => G i ω j - μY j) P
          = gaussianReal 0 ⟨∫ ω, (Y i ω j - μY j) * (Y i ω j - μY j) ∂P,
              integral_nonneg (fun ω => mul_self_nonneg (Y i ω j - μY j))⟩ := by
      intro j
      set u : Fin p → ℝ := fun a => if a = j then (1 : ℝ) else 0 with hu
      have hzero : ∀ b : Fin p, b ≠ j → u b = 0 := by
        intro b hb
        simp [hu, hb]
      have hone : u j = 1 := by
        simp [hu]
      have hfun : (fun ω => ∑ a : Fin p, u a * (G i ω a - μY a))
          = fun ω => G i ω j - μY j := by
        funext ω
        rw [Finset.sum_eq_single j]
        · rw [hone]; ring
        · intro b _ hb; rw [hzero b hb]; ring
        · intro h; exact absurd (Finset.mem_univ j) h
      have hquad : (∑ a : Fin p, ∑ b : Fin p,
            u a * (∫ ω, (Y i ω a - μY a) * (Y i ω b - μY b) ∂P) * u b)
          = ∫ ω, (Y i ω j - μY j) * (Y i ω j - μY j) ∂P := by
        rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single j]
          · rw [hone]; ring
          · intro b _ hb; rw [hzero b hb]; ring
          · intro h; exact absurd (Finset.mem_univ j) h
        · intro a _ ha
          rw [hzero a ha]
          simp
        · intro h; exact absurd (Finset.mem_univ j) h
      have h := IsCenteredGaussianVector.map_linearCombination P (fun ω a => G i ω a - μY a)
        (fun a b => ∫ ω, (Y i ω a - μY a) * (Y i ω b - μY b) ∂P) (hGg i) hPSD u
      rw [← hfun, h]
      exact congrArg (fun v : NNReal => gaussianReal (0 : ℝ) v) (Subtype.ext hquad)
    have hsigma_le : ∀ j : Fin p,
        (∫ ω, (Y i ω j - μY j) * (Y i ω j - μY j) ∂P) ≤ Cvar * B ^ 2 := by
      intro j
      have h := (statopia_math_node_3453903389_21203619 (Ω := Ω) (P := P) B Cvar hBpos hCvar
        (fun ω => Y i ω j - μY j)
        (((measurable_pi_apply j).comp (hYm i)).sub measurable_const) (hYeI i j) (hYe i j)).2.2.2
      simpa [pow_two] using h
    have hraw := statopia_math_node_1099282424_527c2f42 (Ω := Ω) (P := P) p (by omega)
      (Cvar * B ^ 2) (by positivity) (fun (j : Fin p) ω => G i ω j - μY j) hgm
      (fun j => ∫ ω, (Y i ω j - μY j) * (Y i ω j - μY j) ∂P)
      (fun j => integral_nonneg (fun ω => mul_self_nonneg (Y i ω j - μY j))) hsigma_le hlaw
    refine ⟨hraw.1, hraw.2.1, fun s hs => ?_⟩
    have harg : -(s ^ 2) / (2 * (Cvar * B ^ 2)) = -(s ^ 2) / (2 * Cvar * B ^ 2) := by
      rw [← mul_assoc]
    have hne : ENNReal.ofReal (2 * (p : ℝ) * Real.exp (-(s ^ 2) / (2 * (Cvar * B ^ 2)))) ≠ ⊤ :=
      ne_of_lt ENNReal.ofReal_lt_top
    have hstep := ENNReal.toReal_mono hne (hraw.2.2 s hs)
    rw [ENNReal.toReal_ofReal (by positivity), harg] at hstep
    exact hstep
  let C1c : ℝ := 1 / (8 * Real.log 2) + Real.log 2 ^ ((-7 : ℝ) / 2)
  have hC1c_pos : 0 < C1c := by
    have h1 : (0 : ℝ) < 1 / (8 * Real.log 2) := div_pos one_pos (mul_pos (by norm_num) hl2)
    have h2 : (0 : ℝ) < Real.log 2 ^ ((-7 : ℝ) / 2) := Real.rpow_pos_of_pos hl2 _
    exact add_pos h1 h2
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hδabs : 0 < |δ n m| := lt_trans hδ2 (hδ n m hn hm).1
  let tn : ℝ :=
    Real.sqrt (n : ℝ) /
      (4 * (K1 * (B ^ 2 * Real.log (p : ℝ) ^ 4 / (n : ℝ)) ^ ((-1 : ℝ) / 6)) * Real.log (p : ℝ))
  let tm : ℝ :=
    Real.sqrt (m : ℝ) /
      (4 * |δ n m| *
          (K1 * (B ^ 2 * Real.log (p : ℝ) ^ 4 * |δ n m| ^ 6 / (m : ℝ)) ^ ((-1 : ℝ) / 6)) *
        Real.log (p : ℝ))
  have htn_pos : 0 < tn := by
    have hphi : (0 : ℝ) < K1 * (B ^ 2 * Real.log (p : ℝ) ^ 4 / (n : ℝ)) ^ ((-1 : ℝ) / 6) := by
      linarith [hφn_ge]
    exact div_pos (Real.sqrt_pos.mpr hnR) (mul_pos (mul_pos (by norm_num) hphi) hlogp)
  have htm_pos : 0 < tm := by
    have hphi :
        (0 : ℝ) < K1 * (B ^ 2 * Real.log (p : ℝ) ^ 4 * |δ n m| ^ 6 / (m : ℝ)) ^ ((-1 : ℝ) / 6) := by
      linarith [hφm_ge]
    exact div_pos (Real.sqrt_pos.mpr hmR)
      (mul_pos (mul_pos (mul_pos (by norm_num) hδabs) hphi) hlogp)
  have hsqrtc : Real.sqrt Cvar ≤ 1 := Real.sqrt_le_one.mpr hCvar_lt.le
  obtain ⟨hIntX3, hIntF3, hMnb, hMfb⟩ :=
    statopia_math_node_708476089_d6dcc332 (Ω := Ω) (P := P) p n hp (by omega) B C1c Cvar tn hB
      hC1c_pos hCvar_pos hCvar_lt htn_pos xiX xiF (fun i => (hxiX i).1)
      (fun i ω => (hxiX i).2.1 ω) (fun i => (hxiF i).1) (fun i ω => (hxiF i).2.1 ω)
      (fun i s hs => by simpa [neg_div] using (hxiX i).2.2 s hs) (fun i s hs => (hxiF i).2.2 s hs)
      htn_C htn_D htn_E hsqrtc
  obtain ⟨hIntY3, hIntG3, hMmb, hMgb⟩ :=
    statopia_math_node_708476089_d6dcc332 (Ω := Ω) (P := P) p m hp (by omega) B C1c Cvar tm hB
      hC1c_pos hCvar_pos hCvar_lt htm_pos xiY xiG (fun i => (hxiY i).1)
      (fun i ω => (hxiY i).2.1 ω) (fun i => (hxiG i).1) (fun i ω => (hxiG i).2.1 ω)
      (fun i s hs => by simpa [neg_div] using (hxiY i).2.2 s hs) (fun i s hs => (hxiG i).2.2 s hs)
      htm_C htm_D htm_E hsqrtc
  have hLmomX :
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Lmom P X μX
        = LThird P X μX := by
    simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Lmom,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.coordMax,
      LThird, one_div, sSup_range]
  have hLmomY :
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Lmom P Y μY
        = LThird P Y μY := by
    simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Lmom,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.coordMax,
      LThird, one_div, sSup_range]
  have hXmc : ∀ (i : Fin n) (j : Fin p), Measurable fun ω => X i ω j :=
    fun i j => (measurable_pi_apply j).comp (hXm i)
  have hYmc : ∀ (i : Fin m) (j : Fin p), Measurable fun ω => Y i ω j :=
    fun i j => (measurable_pi_apply j).comp (hYm i)
  have hFmc : ∀ (i : Fin n) (j : Fin p), Measurable fun ω => F i ω j :=
    fun i j => (measurable_pi_apply j).comp (hFm i)
  have hGmc : ∀ (i : Fin m) (j : Fin p), Measurable fun ω => G i ω j :=
    fun i j => (measurable_pi_apply j).comp (hGm i)
  have hfam : (fun i => jointFamily X Y F G i) =
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.allVars
        X Y F G := by
    funext i ω
    cases i with
    | inl i => rfl
    | inr i =>
      cases i with
      | inl i => rfl
      | inr i =>
        cases i with
        | inl i => rfl
        | inr i => rfl
  have hindAll : iIndepFun
      (PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.allVars
        X Y F G) P :=
    hfam ▸ hind
  have hkap1 : (1 : ℝ) ≤ kap := by
    rw [one_le_div_iff]
    exact Or.inl ⟨hK1_pos, hK1_le_K1e⟩
  have hkap3 : (1 : ℝ) ≤ kap ^ 3 := by
    have h2 : (1 : ℝ) ≤ kap * kap := by
      have h := mul_le_mul hkap1 hkap1 zero_le_one (le_trans zero_le_one hkap1)
      simpa using h
    have h3 : (1 : ℝ) ≤ (kap * kap) * kap := by
      have h := mul_le_mul h2 hkap1 zero_le_one (mul_nonneg hkap.le hkap.le)
      simpa using h
    calc (1 : ℝ) ≤ (kap * kap) * kap := h3
      _ = kap ^ 3 := by ring
  have hLbar_ge : B ≤ kap ^ 3 * B := by
    have h := mul_le_mul hkap3 (le_refl B) hBpos.le (le_trans zero_le_one hkap3)
    simpa using h
  have hLbar_pos : (0 : ℝ) < kap ^ 3 * B := mul_pos (pow_pos hkap 3) hBpos
  have hLbarX_ne : kap ^ 3 * B ≠ 0 := ne_of_gt hLbar_pos
  have hLbarY_ne : kap ^ 3 * B ≠ 0 := ne_of_gt hLbar_pos
  have hLX' := le_trans (le_of_eq hLmomX) (le_trans hLX hLbar_ge)
  have hLY' := le_trans (le_of_eq hLmomY) (le_trans hLY hLbar_ge)
  have hk6r : (kap ^ 6) ^ (-((1 : ℝ) / 6)) = kap⁻¹ := by
    have h1 : kap ^ (1 : ℝ) = kap := by
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_one]
    rw [← Real.rpow_natCast kap 6, ← Real.rpow_mul hkap.le,
      show ((6 : ℕ) : ℝ) * -((1 : ℝ) / 6) = -1 by norm_num,
      Real.rpow_neg hkap.le (1 : ℝ), h1]
  have hcoef : K1e * kap⁻¹ = K1 := by
    have hk : kap = K1e / K1 := rfl
    have hne : K1e ≠ 0 := ne_of_gt hK1e_pos
    rw [hk, inv_div]
    field_simp
  have hphiN_id :
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiN K1e
          (kap ^ 3 * B) p n
        = K1 * (B ^ 2 * Real.log (p : ℝ) ^ 4 / (n : ℝ)) ^ ((-1 : ℝ) / 6) := by
    have hY : (0 : ℝ) ≤ B ^ 2 * Real.log (p : ℝ) ^ 4 / (n : ℝ) :=
      div_nonneg (mul_nonneg (pow_nonneg hBpos.le 2) (pow_nonneg hlogp.le 4)) hnR.le
    have hk6 : (0 : ℝ) ≤ kap ^ 6 := pow_nonneg hkap.le 6
    simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiN,
      mul_pow, neg_div]
    rw [show (kap ^ 3) ^ 2 = kap ^ 6 by rw [← pow_mul],
      show kap ^ 6 * B ^ 2 * Real.log (p : ℝ) ^ 4 / (n : ℝ)
          = kap ^ 6 * (B ^ 2 * Real.log (p : ℝ) ^ 4 / (n : ℝ)) by
        rw [mul_assoc, mul_div_assoc],
      Real.mul_rpow hk6 hY, hk6r, ← hcoef]
    exact (mul_assoc _ _ _).symm
  have hphiM_id :
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiM K1e
          (kap ^ 3 * B) (δ n m) p m
        = K1 * (B ^ 2 * Real.log (p : ℝ) ^ 4 * |δ n m| ^ 6 / (m : ℝ)) ^ ((-1 : ℝ) / 6) := by
    have hY : (0 : ℝ) ≤ B ^ 2 * Real.log (p : ℝ) ^ 4 * |δ n m| ^ 6 / (m : ℝ) :=
      div_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg hBpos.le 2) (pow_nonneg hlogp.le 4))
          (pow_nonneg (abs_nonneg _) 6)) hmR.le
    have hk6 : (0 : ℝ) ≤ kap ^ 6 := pow_nonneg hkap.le 6
    simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiM,
      mul_pow, neg_div]
    rw [show (kap ^ 3) ^ 2 = kap ^ 6 by ring,
      show kap ^ 6 * B ^ 2 * Real.log (p : ℝ) ^ 4 * |δ n m| ^ 6 / (m : ℝ)
          = kap ^ 6 * (B ^ 2 * Real.log (p : ℝ) ^ 4 * |δ n m| ^ 6 / (m : ℝ)) by ring,
      Real.mul_rpow hk6 hY, hk6r, ← hcoef]
    exact (mul_assoc _ _ _).symm
  have hδne : δ n m ≠ 0 := abs_pos.mp hδabs
  have hXind : iIndepFun X P := by
    have h : iIndepFun (fun i : Fin n => jointFamily X Y F G (Sum.inl i)) P :=
      ProbabilityTheory.iIndepFun.precomp (g := Sum.inl) Sum.inl_injective hind
    simpa [jointFamily] using h
  have hYind : iIndepFun Y P := by
    have h : iIndepFun (fun i : Fin m => jointFamily X Y F G (Sum.inr (Sum.inl i))) P :=
      ProbabilityTheory.iIndepFun.precomp (g := fun i => Sum.inr (Sum.inl i))
        (Sum.inr_injective.comp Sum.inl_injective) hind
    simpa [jointFamily] using h
  have hFind : iIndepFun F P := by
    have h : iIndepFun (fun i : Fin n => jointFamily X Y F G (Sum.inr (Sum.inr (Sum.inl i)))) P :=
      ProbabilityTheory.iIndepFun.precomp (g := fun i => Sum.inr (Sum.inr (Sum.inl i)))
        ((Sum.inr_injective.comp Sum.inr_injective).comp Sum.inl_injective) hind
    simpa [jointFamily] using h
  have hGind : iIndepFun G P := by
    have h : iIndepFun (fun i : Fin m => jointFamily X Y F G (Sum.inr (Sum.inr (Sum.inr i)))) P :=
      ProbabilityTheory.iIndepFun.precomp (g := fun i => Sum.inr (Sum.inr (Sum.inr i)))
        ((Sum.inr_injective.comp Sum.inr_injective).comp Sum.inr_injective) hind
    simpa [jointFamily] using h
  have hsymmF : ∀ (i : Fin n) (j k : Fin p),
      (∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
        = ∫ ω, (X i ω k - μX k) * (X i ω j - μX j) ∂P := by
    intro i j k
    simp only [mul_comm]
  have hsymmG : ∀ (i : Fin m) (j k : Fin p),
      (∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
        = ∫ ω, (Y i ω k - μY k) * (Y i ω j - μY j) ∂P := by
    intro i j k
    simp only [mul_comm]
  have hPSDF : ∀ i : Fin n,
      Matrix.PosSemidef (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P) := by
    intro i
    have h0 := (hFg i).posSemidef_symmetrizedCovariance (p := p) (by omega : 1 ≤ p)
    have h0' :
        ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
          + Matrix.transpose
              (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)))).PosSemidef :=
      h0
    have heq :
        ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
          + Matrix.transpose
              (Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P))))
          = Matrix.of (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P) := by
      ext j k
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
        smul_eq_mul]
      rw [← hsymmF i j k]
      ring
    rw [heq] at h0'
    exact h0'
  have hPSDG : ∀ i : Fin m,
      Matrix.PosSemidef (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P) := by
    intro i
    have h0 := (hGg i).posSemidef_symmetrizedCovariance (p := p) (by omega : 1 ≤ p)
    have h0' :
        ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
          + Matrix.transpose
              (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)))).PosSemidef :=
      h0
    have heq :
        ((2⁻¹ : ℝ) • (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
          + Matrix.transpose
              (Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P))))
          = Matrix.of (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P) := by
      ext j k
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
        smul_eq_mul]
      rw [← hsymmG i j k]
      ring
    rw [heq] at h0'
    exact h0'
  have hSgnnF : ∀ (i : Fin n) (j : Fin p),
      (0 : ℝ) ≤ ∫ ω, (X i ω j - μX j) * (X i ω j - μX j) ∂P :=
    fun i j => integral_nonneg (fun ω => mul_self_nonneg (X i ω j - μX j))
  have hmargF : ∀ (i : Fin n) (j : Fin p),
      Measure.map (fun ω => F i ω j - μX j) P
        = gaussianReal 0 ⟨∫ ω, (X i ω j - μX j) * (X i ω j - μX j) ∂P, hSgnnF i j⟩ := by
    intro i j
    set u : Fin p → ℝ := fun a => if a = j then (1 : ℝ) else 0 with hu
    have hzero : ∀ b : Fin p, b ≠ j → u b = 0 := by
      intro b hb
      simp [hu, hb]
    have hone : u j = 1 := by
      simp [hu]
    have hfun : (fun ω => ∑ a : Fin p, u a * (F i ω a - μX a))
        = fun ω => F i ω j - μX j := by
      funext ω
      rw [Finset.sum_eq_single j]
      · rw [hone]; ring
      · intro b _ hb; rw [hzero b hb]; ring
      · intro h; exact absurd (Finset.mem_univ j) h
    have hquad : (∑ a : Fin p, ∑ b : Fin p,
          u a * (∫ ω, (X i ω a - μX a) * (X i ω b - μX b) ∂P) * u b)
        = ∫ ω, (X i ω j - μX j) * (X i ω j - μX j) ∂P := by
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single j]
        · rw [hone]; ring
        · intro b _ hb; rw [hzero b hb]; ring
        · intro h; exact absurd (Finset.mem_univ j) h
      · intro a _ ha
        rw [hzero a ha]
        simp
      · intro h; exact absurd (Finset.mem_univ j) h
    have h := IsCenteredGaussianVector.map_linearCombination P (fun ω a => F i ω a - μX a)
      (fun a b => ∫ ω, (X i ω a - μX a) * (X i ω b - μX b) ∂P) (hFg i) (hPSDF i) u
    rw [← hfun, h]
    exact congrArg (fun v : NNReal => gaussianReal (0 : ℝ) v) (Subtype.ext hquad)
  
  
  have hFsq : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => (F i ω j - μX j) ^ 2) P := by
    intro i j
    have hmem : MemLp (fun x : ℝ => x ^ 2) 1 (Measure.map (fun ω => F i ω j - μX j) P) := by
      rw [hmargF i j]
      exact memLp_pow_id_gaussianReal 2 1 (by simp)
    have hcomp : MemLp (fun ω => (F i ω j - μX j) ^ 2) 1 P :=
      hmem.comp_of_map ((hFmc i j).sub measurable_const).aemeasurable
    exact memLp_one_iff_integrable.mp hcomp
  have hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - μX j| ^ 3) P := by
    intro i j
    have hmem : MemLp (fun x : ℝ => x ^ 3) 1 (Measure.map (fun ω => F i ω j - μX j) P) := by
      rw [hmargF i j]
      exact memLp_pow_id_gaussianReal 3 1 (by simp)
    have hcomp : MemLp (fun ω => (F i ω j - μX j) ^ 3) 1 P :=
      hmem.comp_of_map ((hFmc i j).sub measurable_const).aemeasurable
    have h2 := (memLp_one_iff_integrable.mp hcomp).norm
    simpa [Real.norm_eq_abs, abs_pow] using h2
  have hF2 :
      ∀ (i : Fin n) (j k : Fin p),
        Integrable (fun ω => (F i ω j - μX j) * (F i ω k - μX k)) P := by
    intro i j k
    refine ((hFsq i j).add (hFsq i k)).mono'
      (((hFmc i j).sub measurable_const).mul
        ((hFmc i k).sub measurable_const)).aestronglyMeasurable ?_
    filter_upwards with ω
    have hsq : (0 : ℝ) ≤ (|F i ω j - μX j| - |F i ω k - μX k|) ^ 2 := sq_nonneg _
    have hexp : (|F i ω j - μX j| - |F i ω k - μX k|) ^ 2
        = |F i ω j - μX j| ^ 2 - 2 * |F i ω j - μX j| * |F i ω k - μX k|
          + |F i ω k - μX k| ^ 2 := by ring
    have h3 : |F i ω j - μX j| ^ 2 = (F i ω j - μX j) ^ 2 := sq_abs _
    have h4 : |F i ω k - μX k| ^ 2 = (F i ω k - μX k) ^ 2 := sq_abs _
    have hnn : (0 : ℝ) ≤ |F i ω j - μX j| * |F i ω k - μX k| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul]
    show |F i ω j - μX j| * |F i ω k - μX k|
      ≤ (F i ω j - μX j) ^ 2 + (F i ω k - μX k) ^ 2
    linarith
  have hFchild := fun i : Fin n =>
    statopia_math_node_3590859496_cde24528 (Ω := Ω) (P := P) p (by omega)
      (fun ω j => F i ω j - μX j)
      (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
      (fun j => (hFmc i j).sub measurable_const) (hFg i) (hsymmF i) (hF2 i)
  have hFint : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => F i ω j) P := by
    intro i j
    have h : Integrable (fun ω => (F i ω j - μX j) + μX j) P :=
      ((hFchild i).1 j).add (integrable_const (μX j))
    simpa only [sub_add_cancel] using h
  have hFμ : ∀ (i : Fin n) (j : Fin p), ∫ (ω : Ω), F i ω j ∂P = μX j := by
    intro i j
    have hstep : ∫ (ω : Ω), ((F i ω j - μX j) + μX j) ∂P
        = ∫ (ω : Ω), (F i ω j - μX j) ∂P + ∫ (ω : Ω), μX j ∂P :=
      integral_add ((hFchild i).1 j) (integrable_const (μX j))
    have hthis : ∫ (ω : Ω), ((F i ω j - μX j) + μX j) ∂P = μX j := by
      rw [hstep, (hFchild i).2.1 j]
      simp
    simpa only [sub_add_cancel] using hthis
  have hFcov :
      ∀ (i : Fin n) (j k : Fin p),
        ∫ (ω : Ω), (F i ω j - μX j) * (F i ω k - μX k) ∂P
          = ∫ (ω : Ω), (X i ω j - μX j) * (X i ω k - μX k) ∂P := by
    intro i j k
    exact statopia_math_node_343663452_95962ec5 (Ω := Ω) (P := P) p (by omega)
      (fun ω j => F i ω j - μX j)
      (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)
      (fun j => (hFmc i j).sub measurable_const) (hFg i) (hsymmF i) (hF2 i) j k
  have hSgnnG : ∀ (i : Fin m) (j : Fin p),
      (0 : ℝ) ≤ ∫ ω, (Y i ω j - μY j) * (Y i ω j - μY j) ∂P :=
    fun i j => integral_nonneg (fun ω => mul_self_nonneg (Y i ω j - μY j))
  have hmargG : ∀ (i : Fin m) (j : Fin p),
      Measure.map (fun ω => G i ω j - μY j) P
        = gaussianReal 0 ⟨∫ ω, (Y i ω j - μY j) * (Y i ω j - μY j) ∂P, hSgnnG i j⟩ := by
    intro i j
    set u : Fin p → ℝ := fun a => if a = j then (1 : ℝ) else 0 with hu
    have hzero : ∀ b : Fin p, b ≠ j → u b = 0 := by
      intro b hb
      simp [hu, hb]
    have hone : u j = 1 := by
      simp [hu]
    have hfun : (fun ω => ∑ a : Fin p, u a * (G i ω a - μY a))
        = fun ω => G i ω j - μY j := by
      funext ω
      rw [Finset.sum_eq_single j]
      · rw [hone]; ring
      · intro b _ hb; rw [hzero b hb]; ring
      · intro h; exact absurd (Finset.mem_univ j) h
    have hquad : (∑ a : Fin p, ∑ b : Fin p,
          u a * (∫ ω, (Y i ω a - μY a) * (Y i ω b - μY b) ∂P) * u b)
        = ∫ ω, (Y i ω j - μY j) * (Y i ω j - μY j) ∂P := by
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single j]
        · rw [hone]; ring
        · intro b _ hb; rw [hzero b hb]; ring
        · intro h; exact absurd (Finset.mem_univ j) h
      · intro a _ ha
        rw [hzero a ha]
        simp
      · intro h; exact absurd (Finset.mem_univ j) h
    have h := IsCenteredGaussianVector.map_linearCombination P (fun ω a => G i ω a - μY a)
      (fun a b => ∫ ω, (Y i ω a - μY a) * (Y i ω b - μY b) ∂P) (hGg i) (hPSDG i) u
    rw [← hfun, h]
    exact congrArg (fun v : NNReal => gaussianReal (0 : ℝ) v) (Subtype.ext hquad)
  have hGsq : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => (G i ω j - μY j) ^ 2) P := by
    intro i j
    have hmem : MemLp (fun x : ℝ => x ^ 2) 1 (Measure.map (fun ω => G i ω j - μY j) P) := by
      rw [hmargG i j]
      exact memLp_pow_id_gaussianReal 2 1 (by simp)
    have hcomp : MemLp (fun ω => (G i ω j - μY j) ^ 2) 1 P :=
      hmem.comp_of_map ((hGmc i j).sub measurable_const).aemeasurable
    exact memLp_one_iff_integrable.mp hcomp
  have hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - μY j| ^ 3) P := by
    intro i j
    have hmem : MemLp (fun x : ℝ => x ^ 3) 1 (Measure.map (fun ω => G i ω j - μY j) P) := by
      rw [hmargG i j]
      exact memLp_pow_id_gaussianReal 3 1 (by simp)
    have hcomp : MemLp (fun ω => (G i ω j - μY j) ^ 3) 1 P :=
      hmem.comp_of_map ((hGmc i j).sub measurable_const).aemeasurable
    have h2 := (memLp_one_iff_integrable.mp hcomp).norm
    simpa [Real.norm_eq_abs, abs_pow] using h2
  have hG2 :
      ∀ (i : Fin m) (j k : Fin p),
        Integrable (fun ω => (G i ω j - μY j) * (G i ω k - μY k)) P := by
    intro i j k
    refine ((hGsq i j).add (hGsq i k)).mono'
      (((hGmc i j).sub measurable_const).mul
        ((hGmc i k).sub measurable_const)).aestronglyMeasurable ?_
    filter_upwards with ω
    have hsq : (0 : ℝ) ≤ (|G i ω j - μY j| - |G i ω k - μY k|) ^ 2 := sq_nonneg _
    have hexp : (|G i ω j - μY j| - |G i ω k - μY k|) ^ 2
        = |G i ω j - μY j| ^ 2 - 2 * |G i ω j - μY j| * |G i ω k - μY k|
          + |G i ω k - μY k| ^ 2 := by ring
    have h3 : |G i ω j - μY j| ^ 2 = (G i ω j - μY j) ^ 2 := sq_abs _
    have h4 : |G i ω k - μY k| ^ 2 = (G i ω k - μY k) ^ 2 := sq_abs _
    have hnn : (0 : ℝ) ≤ |G i ω j - μY j| * |G i ω k - μY k| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul]
    show |G i ω j - μY j| * |G i ω k - μY k|
      ≤ (G i ω j - μY j) ^ 2 + (G i ω k - μY k) ^ 2
    linarith
  have hGchild := fun i : Fin m =>
    statopia_math_node_3590859496_cde24528 (Ω := Ω) (P := P) p (by omega)
      (fun ω j => G i ω j - μY j)
      (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
      (fun j => (hGmc i j).sub measurable_const) (hGg i) (hsymmG i) (hG2 i)
  have hGint : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => G i ω j) P := by
    intro i j
    have h : Integrable (fun ω => (G i ω j - μY j) + μY j) P :=
      ((hGchild i).1 j).add (integrable_const (μY j))
    simpa only [sub_add_cancel] using h
  have hGμ : ∀ (i : Fin m) (j : Fin p), ∫ (ω : Ω), G i ω j ∂P = μY j := by
    intro i j
    have hstep : ∫ (ω : Ω), ((G i ω j - μY j) + μY j) ∂P
        = ∫ (ω : Ω), (G i ω j - μY j) ∂P + ∫ (ω : Ω), μY j ∂P :=
      integral_add ((hGchild i).1 j) (integrable_const (μY j))
    have hthis : ∫ (ω : Ω), ((G i ω j - μY j) + μY j) ∂P = μY j := by
      rw [hstep, (hGchild i).2.1 j]
      simp
    simpa only [sub_add_cancel] using hthis
  have hGcov :
      ∀ (i : Fin m) (j k : Fin p),
        ∫ (ω : Ω), (G i ω j - μY j) * (G i ω k - μY k) ∂P
          = ∫ (ω : Ω), (Y i ω j - μY j) * (Y i ω k - μY k) ∂P := by
    intro i j k
    exact statopia_math_node_343663452_95962ec5 (Ω := Ω) (P := P) p (by omega)
      (fun ω j => G i ω j - μY j)
      (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)
      (fun j => (hGmc i j).sub measurable_const) (hGg i) (hsymmG i) (hG2 i) j k
  have htrans : ∀ (c : Fin p → ℝ) (V : Ω → Fin p → ℝ), Measurable V →
      IsGaussian (Measure.map (fun ω j => V ω j - c j) P) → IsGaussian (Measure.map V P) := by
    intro c V hV hG
    haveI hGi : IsGaussian (Measure.map (fun ω j => V ω j - c j) P) := hG
    refine isGaussian_of_isGaussian_map ?_
    intro L
    have hZg : IsGaussian (Measure.map L (Measure.map (fun ω j => V ω j - c j) P)) :=
      isGaussian_map L
    obtain ⟨m, v, hmv⟩ : ∃ (m : ℝ) (v : NNReal),
        Measure.map L (Measure.map (fun ω j => V ω j - c j) P) = gaussianReal m v :=
      ⟨_, _, IsGaussian.eq_gaussianReal _ hZg⟩
    have hkey : Measure.map L (Measure.map V P) = gaussianReal (m + L c) v := by
      have h1 : Measure.map L (Measure.map V P) = Measure.map (fun ω => L (V ω)) P := by
        first
          | exact Measure.map_map L.continuous.measurable
          | exact Measure.map_map hV L.continuous.measurable
          | exact Measure.map_map L.continuous.measurable hV
      have h2 : (fun ω => L (V ω)) = fun ω => L (fun j => V ω j - c j) + L c := by
        funext ω
        rw [show L (V ω) = L ((fun j => V ω j - c j) + c) from by
          congr 1
          funext j
          simp, map_add]
      have h3 : Measure.map (fun ω => L (fun j => V ω j - c j) + L c) P
          = Measure.map (fun x : ℝ => x + L c)
              (Measure.map (fun ω => L (fun j => V ω j - c j)) P) := by
        first
          | exact (Measure.map_map (measurable_id.add measurable_const)).symm
          | exact (Measure.map_map (L.continuous.measurable.comp (hV.sub measurable_const))
              (measurable_id.add measurable_const)).symm
          | exact (Measure.map_map (measurable_id.add measurable_const)
              (L.continuous.measurable.comp (hV.sub measurable_const))).symm
          | exact (Measure.map_map ((hV.sub measurable_const).comp L.continuous.measurable)
              (measurable_id.add measurable_const)).symm
          | exact (Measure.map_map (measurable_id.add measurable_const)
              ((hV.sub measurable_const).comp L.continuous.measurable)).symm
      have h4 : Measure.map (fun ω => L (fun j => V ω j - c j)) P
          = Measure.map L (Measure.map (fun ω j => V ω j - c j) P) := by
        first
          | exact (Measure.map_map L.continuous.measurable).symm
          | exact (Measure.map_map L.continuous.measurable (hV.sub measurable_const)).symm
          | exact (Measure.map_map (hV.sub measurable_const) L.continuous.measurable).symm
      rw [h1, h2, h3, h4, hmv, gaussianReal_map_add_const]
    rw [hkey]
    exact isGaussian_gaussianReal _ _
  have hFgauss : ∀ (i : Fin n), IsGaussian (Measure.map (F i) P) :=
    fun i => htrans μX (F i) (hFm i) (hFchild i).2.2.2.2.2.2
  have hGgauss : ∀ (i : Fin m), IsGaussian (Measure.map (G i) P) :=
    fun i => htrans μY (G i) (hGm i) (hGchild i).2.2.2.2.2.2
  have hcombVec_eq :
      ∀ (ω : Ω) (j : Fin p),
        PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec
            X Y μX μY (δ n m) ω j
          = combinedStat n m (δ n m) μX μY X Y ω j := by
    intro ω j
    simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.normSum,
      combinedStat, normalizedSum, one_div]
    ring
  have hcombVecI :
      ∀ (j : Fin p),
        Integrable
          (fun ω =>
            PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec
                X Y μX μY (δ n m) ω j ^ 2) P :=
    fun j => by simpa only [hcombVec_eq] using hcombI j
  have hcombVecv :
      ∀ (j : Fin p),
        b ≤ ∫ (ω : Ω),
          PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec
              X Y μX μY (δ n m) ω j ^ 2 ∂P :=
    fun j => by simpa only [hcombVec_eq] using hbv j
  have hphiNge :
      2 ≤ PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiN
        K1e (kap ^ 3 * B) p n := by
    rw [hphiN_id]
    exact hφn_ge
  have hphiMge :
      2 ≤ PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiM
        K1e (kap ^ 3 * B) (δ n m) p m := by
    rw [hphiM_id]
    exact hφm_ge
  have hXsq : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => (X i ω j - μX j) ^ 2) P :=
    fun i j => by simpa [pow_two] using hX2 i j j
  have hYsq : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => (Y i ω j - μY j) ^ 2) P :=
    fun i j => by simpa [pow_two] using hY2 i j j
  have hρ :=
    hL4 n m p hn hm hp δ hδne P X Y F G μX μY (kap ^ 3 * B) (kap ^ 3 * B) hXmc hYmc hFmc hGmc
      hXind hYind hFind hGind hindAll hXi hXμ hYi hYμ hXsq hX3 hX2 hYsq hY3 hY2 hFint hFμ hFsq
      hF3 hF2 hFcov hGint hGμ hGsq hG3 hG2 hGcov hFgauss hGgauss hcombVecI hcombVecv hLX' hLY'
      hLbarX_ne hLbarY_ne hphiNge hphiMge
  have hbridge :
      rhoStarStar P (combinedStat n m (δ n m) μX μY X Y) (combinedStat n m (δ n m) μX μY F G)
        ≤ PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.rho
            P
            (PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec
              X Y μX μY (δ n m))
            (PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec
              F G μX μY (δ n m)) := by
    have hZ1 : combinedStat n m (δ n m) μX μY X Y
        = PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec
            X Y μX μY (δ n m) := by
      funext ω j
      exact (hcombVec_eq ω j).symm
    have hZ2 : combinedStat n m (δ n m) μX μY F G
        = PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec
            F G μX μY (δ n m) := by
      funext ω j
      simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.combVec,
        PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.normSum,
        combinedStat, normalizedSum, one_div]
      ring
    rw [hZ1, hZ2]
    apply le_of_eq
    simp only [rhoStarStar,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.rho]
    first
      | rfl
      | (congr 1
         ext t
         simp only [Set.mem_setOf_eq, Set.mem_image]
         constructor
         · rintro ⟨A, hA, ht⟩
           refine ⟨A, hA, ?_⟩
           first
             | exact ht
             | exact ht.symm
         · rintro ⟨A, hA, ht⟩
           refine ⟨A, hA, ?_⟩
           first
             | exact ht
             | exact ht.symm)
  set Mnv : ℝ :=
    PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Mn P X F μX
      (PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiN
        K1e (kap ^ 3 * B) p n) with hMndef
  set Mmv : ℝ :=
    PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.MmStar P Y G μY
      (δ n m)
      (PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.phiM
        K1e (kap ^ 3 * B) (δ n m) p m) with hMmdef
  have hMn_eq :
      Mnv
        = (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ (ω : Ω), xiX i ω ^ 3 * (if xiX i ω > tn then 1 else 0) ∂P
          + (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ (ω : Ω), xiF i ω ^ 3 * (if xiF i ω > tn then 1 else 0) ∂P := by
    rw [hMndef]
    simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Mn,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Mtrunc,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.coordMax,
      hphiN_id, gt_iff_lt, mul_ite, mul_one, mul_zero, sSup_range, Set.indicator_apply,
      Set.mem_setOf_eq]
    rfl
  have hMm_eq :
      Mmv
        = (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ (ω : Ω), xiY i ω ^ 3 * (if xiY i ω > tm then 1 else 0) ∂P
          + (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ (ω : Ω), xiG i ω ^ 3 * (if xiG i ω > tm then 1 else 0) ∂P := by
    rw [hMmdef]
    simp only [PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.MmStar,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.Mtrunc,
      PaperProofTasks.job_paper_2d165b9668ee43088292ee6f2129e2cd.Statlib.Imported.XuYaoL4.coordMax,
      hphiM_id, gt_iff_lt, mul_ite, mul_one, mul_zero, sSup_range, Set.indicator_apply,
      Set.mem_setOf_eq]
    rfl
  have hMn_le : Mnv ≤ CM / Real.sqrt (n : ℝ) := by
    rw [hMn_eq]
    have h12 : 12 * C1c ^ 3 / Real.sqrt (n : ℝ) + 20 * C1c ^ 3 / Real.sqrt (n : ℝ)
        = CM / Real.sqrt (n : ℝ) := by
      have hCMeq : CM = 32 * C1c ^ 3 := rfl
      rw [hCMeq]
      rw [← add_div, ← add_mul]
      norm_num
    have hb1 := hMnb
    rw [one_div] at hb1
    have hb2 := hMfb
    rw [one_div] at hb2
    linarith [h12]
  have hMm_le : Mmv ≤ CM / Real.sqrt (m : ℝ) := by
    rw [hMm_eq]
    have h12 : 12 * C1c ^ 3 / Real.sqrt (m : ℝ) + 20 * C1c ^ 3 / Real.sqrt (m : ℝ)
        = CM / Real.sqrt (m : ℝ) := by
      have hCMeq : CM = 32 * C1c ^ 3 := rfl
      rw [hCMeq]
      rw [← add_div, ← add_mul]
      norm_num
    have hb1 := hMmb
    rw [one_div] at hb1
    have hb2 := hMgb
    rw [one_div] at hb2
    linarith [h12]
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0R : (0 : ℝ) < (p : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpn_le : (p : ℝ) ≤ (p : ℝ) * (n : ℝ) := by
    have h : (p : ℝ) * 1 ≤ (p : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 hp0R.le
    simpa using h
  have hpm_le : (p : ℝ) ≤ (p : ℝ) * (m : ℝ) := by
    have h : (p : ℝ) * 1 ≤ (p : ℝ) * (m : ℝ) := mul_le_mul_of_nonneg_left hm1 hp0R.le
    simpa using h
  have hlogpn : Real.log (p : ℝ) ≤ Real.log ((p : ℝ) * (n : ℝ)) := Real.log_le_log hp0R hpn_le
  have hlogpm : Real.log (p : ℝ) ≤ Real.log ((p : ℝ) * (m : ℝ)) := Real.log_le_log hp0R hpm_le
  have hpn_gt : (1 : ℝ) < (p : ℝ) * (n : ℝ) := by
    calc (1 : ℝ) < (p : ℝ) := hp2
      _ = (p : ℝ) * 1 := (mul_one _).symm
      _ ≤ (p : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 hp0R.le
  have hpm_gt : (1 : ℝ) < (p : ℝ) * (m : ℝ) := by
    calc (1 : ℝ) < (p : ℝ) := hp2
      _ = (p : ℝ) * 1 := (mul_one _).symm
      _ ≤ (p : ℝ) * (m : ℝ) := mul_le_mul_of_nonneg_left hm1 hp0R.le
  have hlogn_pos : (0 : ℝ) < Real.log ((p : ℝ) * (n : ℝ)) := Real.log_pos hpn_gt
  have hlogm_pos : (0 : ℝ) < Real.log ((p : ℝ) * (m : ℝ)) := Real.log_pos hpm_gt
  have hbaseN_pos : (0 : ℝ) < B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ) :=
    div_pos (mul_pos (pow_pos hBpos 2) (pow_pos hlogn_pos 7)) hnR
  have hbaseM_pos : (0 : ℝ) < B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ) :=
    div_pos (mul_pos (pow_pos hBpos 2) (pow_pos hlogm_pos 7)) hmR
  have hQn_nonneg :
      (0 : ℝ) ≤ (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) :=
    (Real.rpow_pos_of_pos hbaseN_pos ((1 : ℝ) / 6)).le
  have hQm_nonneg :
      (0 : ℝ) ≤ (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) :=
    (Real.rpow_pos_of_pos hbaseM_pos ((1 : ℝ) / 6)).le
  have hlogpn7 : Real.log (p : ℝ) ^ 7 ≤ Real.log ((p : ℝ) * (n : ℝ)) ^ 7 :=
    pow_le_pow_left₀ hlogp.le hlogpn 7
  have hlogpm7 : Real.log (p : ℝ) ^ 7 ≤ Real.log ((p : ℝ) * (m : ℝ)) ^ 7 :=
    pow_le_pow_left₀ hlogp.le hlogpm 7
  have hbase_le_n :
      B ^ 2 * Real.log (p : ℝ) ^ 7 / (n : ℝ)
        ≤ B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogpn7 (pow_nonneg hBpos.le 2))
      (le_of_lt (inv_pos.mpr hnR))
  have hbase_le_m :
      B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)
        ≤ B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogpm7 (pow_nonneg hBpos.le 2))
      (le_of_lt (inv_pos.mpr hmR))
  have hQn_le :
      (B ^ 2 * Real.log (p : ℝ) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6)
        ≤ (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) :=
    Real.rpow_le_rpow
      (div_nonneg (mul_nonneg (pow_nonneg hBpos.le 2) (pow_nonneg hlogp.le 7)) hnR.le)
      hbase_le_n (by norm_num)
  have hQm_le :
      (B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6)
        ≤ (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) :=
    Real.rpow_le_rpow
      (div_nonneg (mul_nonneg (pow_nonneg hBpos.le 2) (pow_nonneg hlogp.le 7)) hmR.le)
      hbase_le_m (by norm_num)
  have hxNp : (0 : ℝ) ≤ B ^ 2 * Real.log (p : ℝ) ^ 7 / (n : ℝ) :=
    div_nonneg (mul_nonneg (pow_nonneg hBpos.le 2) (pow_nonneg hlogp.le 7)) hnR.le
  have hxMp : (0 : ℝ) ≤ B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ) :=
    div_nonneg (mul_nonneg (pow_nonneg hBpos.le 2) (pow_nonneg hlogp.le 7)) hmR.le
  have hk6p : (kap ^ 6) ^ ((1 : ℝ) / 6) = kap := by
    rw [← Real.rpow_natCast kap 6, ← Real.rpow_mul hkap.le,
      show ((6 : ℕ) : ℝ) * ((1 : ℝ) / 6) = ((1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, pow_one]
  have hkeyA : ∀ (a b c d : ℝ), (a ^ 3 * b) ^ 2 * c ^ 7 / d = a ^ 6 * (b ^ 2 * c ^ 7 / d) := by
    intro a b c d
    rw [mul_pow, ← pow_mul, ← mul_div_assoc, ← mul_assoc]
  have ht1 :
      ((kap ^ 3 * B) ^ 2 * Real.log (p : ℝ) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6)
        = kap * (B ^ 2 * Real.log (p : ℝ) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) := by
    rw [hkeyA kap B (Real.log (p : ℝ)) (n : ℝ),
      Real.mul_rpow (pow_nonneg hkap.le 6) hxNp, hk6p]
  have ht1_le :
      ((kap ^ 3 * B) ^ 2 * Real.log (p : ℝ) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6)
        ≤ kap * (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) := by
    rw [ht1]
    exact mul_le_mul_of_nonneg_left hQn_le hkap.le
  have hkeyC : ∀ (a c e d : ℝ), a * c ^ 7 * e ^ 6 / d = (a * c ^ 7 / d) * e ^ 6 := by
    intro a c e d
    rw [div_mul_eq_mul_div]
  have hkeyB : ∀ (a b c e d : ℝ),
      (a ^ 3 * b) ^ 2 * c ^ 7 * e ^ 6 / d = a ^ 6 * (b ^ 2 * c ^ 7 * e ^ 6 / d) := by
    intro a b c e d
    rw [mul_pow, ← pow_mul, mul_div_assoc, mul_div_assoc, mul_assoc, mul_assoc, mul_assoc]
  have hdelta6 : (|δ n m| ^ 6) ^ ((1 : ℝ) / 6) = |δ n m| := by
    rw [← Real.rpow_natCast (|δ n m|) 6, ← Real.rpow_mul (abs_nonneg (δ n m)),
      show ((6 : ℕ) : ℝ) * ((1 : ℝ) / 6) = ((1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, pow_one]
  have hxMd : (0 : ℝ) ≤ B ^ 2 * Real.log (p : ℝ) ^ 7 * |δ n m| ^ 6 / (m : ℝ) :=
    div_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg hBpos.le 2) (pow_nonneg hlogp.le 7))
        (pow_nonneg (abs_nonneg (δ n m)) 6)) hmR.le
  have hxrM : (0 : ℝ) ≤ (B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) :=
    (Real.rpow_pos_of_pos (div_pos (mul_pos (pow_pos hBpos 2) (pow_pos hlogp 7)) hmR)
      ((1 : ℝ) / 6)).le
  have hsplitM :
      (B ^ 2 * Real.log (p : ℝ) ^ 7 * |δ n m| ^ 6 / (m : ℝ)) ^ ((1 : ℝ) / 6)
        = (B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * |δ n m| := by
    rw [hkeyC (B ^ 2) (Real.log (p : ℝ)) (|δ n m|) (m : ℝ),
      Real.mul_rpow hxMp (pow_nonneg (abs_nonneg (δ n m)) 6), hdelta6]
  have ht3 :
      ((kap ^ 3 * B) ^ 2 * Real.log (p : ℝ) ^ 7 * |δ n m| ^ 6 / (m : ℝ)) ^ ((1 : ℝ) / 6)
        = kap * ((B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * |δ n m|) := by
    rw [hkeyB kap B (Real.log (p : ℝ)) (|δ n m|) (m : ℝ),
      Real.mul_rpow (pow_nonneg hkap.le 6) hxMd, hk6p, hsplitM]
  have ht3_le :
      ((kap ^ 3 * B) ^ 2 * Real.log (p : ℝ) ^ 7 * |δ n m| ^ 6 / (m : ℝ)) ^ ((1 : ℝ) / 6)
        ≤ δ1 * kap * (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) := by
    rw [ht3]
    have hδle : |δ n m| ≤ δ1 := (hδ n m hn hm).2.le
    have h1 :
        (B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * |δ n m|
          ≤ (B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * δ1 :=
      mul_le_mul_of_nonneg_left hδle hxrM
    have h2 :
        (B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * δ1
          ≤ (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * δ1 :=
      mul_le_mul_of_nonneg_right hQm_le hδ1.le
    calc kap * ((B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * |δ n m|)
        ≤ kap * ((B ^ 2 * Real.log (p : ℝ) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * δ1) :=
          mul_le_mul_of_nonneg_left h1 hkap.le
      _ ≤ kap * ((B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) * δ1) :=
          mul_le_mul_of_nonneg_left h2 hkap.le
      _ = δ1 * kap * (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) := by
          ac_rfl
  have hleft7 : (Real.log 2 ^ 7) ^ ((1 : ℝ) / 6) = Real.log 2 ^ ((7 : ℝ) / 6) := by
    rw [← Real.rpow_natCast (Real.log 2) 7, ← Real.rpow_mul hl2.le,
      show ((7 : ℕ) : ℝ) * ((1 : ℝ) / 6) = (7 : ℝ) / 6 by norm_num]
  have hone7 : Real.log 2 ^ ((-7 : ℝ) / 6) * Real.log 2 ^ ((7 : ℝ) / 6) = 1 := by
    rw [show ((-7 : ℝ) / 6) = -((7 : ℝ) / 6) by norm_num, Real.rpow_neg hl2.le,
      inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hl2 ((7 : ℝ) / 6)))]
  have hBpow : ∀ k : ℕ, (1 : ℝ) ≤ B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h := mul_le_mul ih hB zero_le_one (le_trans zero_le_one ih)
        simpa [pow_succ] using h
  have hkeygen : ∀ (N : ℕ), 0 < N → (1 : ℝ) ≤ (N : ℝ) →
      1 / (Real.sqrt (N : ℝ) * B)
        ≤ Real.log 2 ^ ((-7 : ℝ) / 6) *
            (B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) ^ ((1 : ℝ) / 6) := by
    intro N hN hN1
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1pN : (1 : ℝ) < (p : ℝ) * (N : ℝ) := by
      have h := mul_le_mul hp2R hN1 (zero_le_one : (0 : ℝ) ≤ 1) hp0R.le
      linarith
    have hlogN_pos : (0 : ℝ) < Real.log ((p : ℝ) * (N : ℝ)) := Real.log_pos h1pN
    have hbaseN : (0 : ℝ) < B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ) :=
      div_pos (mul_pos (pow_pos hBpos 2) (pow_pos hlogN_pos 7)) hNR
    have hpN_le : (p : ℝ) ≤ (p : ℝ) * (N : ℝ) := by
      have h : (p : ℝ) * 1 ≤ (p : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left hN1 hp0R.le
      simpa using h
    have hlogpN : Real.log (p : ℝ) ≤ Real.log ((p : ℝ) * (N : ℝ)) := Real.log_le_log hp0R hpN_le
    have hL7 : Real.log (p : ℝ) ^ 7 ≤ Real.log ((p : ℝ) * (N : ℝ)) ^ 7 :=
      pow_le_pow_left₀ hlogp.le hlogpN 7
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) hN1 2
      simpa using h
    have hBN : (1 : ℝ) ≤ B ^ 8 * (N : ℝ) ^ 2 := by
      have h := mul_le_mul (hBpow 8) hN2 zero_le_one (le_trans zero_le_one (hBpow 8))
      simpa using h
    have hlog2N : Real.log 2 ≤ Real.log ((p : ℝ) * (N : ℝ)) := by
      refine Real.log_le_log (by norm_num) ?_
      have h := mul_le_mul hp2R hN1 (zero_le_one : (0 : ℝ) ≤ 1) hp0R.le
      linarith
    have hlog2_7 : Real.log 2 ^ 7 ≤ Real.log ((p : ℝ) * (N : ℝ)) ^ 7 :=
      pow_le_pow_left₀ hl2.le hlog2N 7
    have hbig : Real.log 2 ^ 7 ≤ B ^ 8 * (N : ℝ) ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 := by
      have h0 : (0 : ℝ) ≤ Real.log 2 ^ 7 := pow_nonneg hl2.le 7
      have h2 : Real.log 2 ^ 7 ≤ (B ^ 8 * (N : ℝ) ^ 2) * Real.log 2 ^ 7 := by
        calc Real.log 2 ^ 7 = 1 * Real.log 2 ^ 7 := (one_mul _).symm
          _ ≤ (B ^ 8 * (N : ℝ) ^ 2) * Real.log 2 ^ 7 :=
              mul_le_mul hBN (le_refl _) h0 (le_trans zero_le_one hBN)
      calc Real.log 2 ^ 7 ≤ (B ^ 8 * (N : ℝ) ^ 2) * Real.log 2 ^ 7 := h2
        _ ≤ (B ^ 8 * (N : ℝ) ^ 2) * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 :=
            mul_le_mul_of_nonneg_left hlog2_7 (le_trans zero_le_one hBN)
    have hsqrtN6 : (Real.sqrt (N : ℝ)) ^ 6 = (N : ℝ) ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hNR.le]
    have hsB6 : (Real.sqrt (N : ℝ) * B) ^ 6 = (N : ℝ) ^ 3 * B ^ 6 := by
      rw [mul_pow, hsqrtN6]
    have hzero : (0 : ℝ) ≤ Real.sqrt (N : ℝ) * B :=
      (mul_pos (Real.sqrt_pos.mpr hNR) hBpos).le
    have hsB : ((Real.sqrt (N : ℝ) * B) ^ 6) ^ ((1 : ℝ) / 6) = Real.sqrt (N : ℝ) * B := by
      rw [← Real.rpow_natCast (Real.sqrt (N : ℝ) * B) 6, ← Real.rpow_mul hzero,
        show ((6 : ℕ) : ℝ) * ((1 : ℝ) / 6) = ((1 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, pow_one]
    have hcombine :
        (B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) * (Real.sqrt (N : ℝ) * B) ^ 6
          = B ^ 8 * (N : ℝ) ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 := by
      rw [hsB6]
      field_simp
    have hmul :
        (B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) ^ ((1 : ℝ) / 6)
            * ((Real.sqrt (N : ℝ) * B) ^ 6) ^ ((1 : ℝ) / 6)
          = ((B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ))
              * (Real.sqrt (N : ℝ) * B) ^ 6) ^ ((1 : ℝ) / 6) :=
      (Real.mul_rpow hbaseN.le (pow_nonneg hzero 6)).symm
    have hexp :
        ((B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ))
            * (Real.sqrt (N : ℝ) * B) ^ 6) ^ ((1 : ℝ) / 6)
          = (B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) ^ ((1 : ℝ) / 6)
            * (Real.sqrt (N : ℝ) * B) := by
      rw [← hmul, hsB]
    have hroot : Real.log 2 ^ ((7 : ℝ) / 6)
        ≤ (B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) ^ ((1 : ℝ) / 6)
            * (Real.sqrt (N : ℝ) * B) := by
      have h1 : (Real.log 2 ^ 7) ^ ((1 : ℝ) / 6)
          ≤ (B ^ 8 * (N : ℝ) ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7) ^ ((1 : ℝ) / 6) :=
        Real.rpow_le_rpow (pow_nonneg hl2.le 7) hbig (by norm_num)
      calc Real.log 2 ^ ((7 : ℝ) / 6) = (Real.log 2 ^ 7) ^ ((1 : ℝ) / 6) := hleft7.symm
        _ ≤ (B ^ 8 * (N : ℝ) ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7) ^ ((1 : ℝ) / 6) := h1
        _ = ((B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) *
              (Real.sqrt (N : ℝ) * B) ^ 6) ^ ((1 : ℝ) / 6) := by rw [hcombine]
        _ = (B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) ^ ((1 : ℝ) / 6)
              * (Real.sqrt (N : ℝ) * B) := hexp
    rw [div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hNR) hBpos)]
    calc (1 : ℝ) = Real.log 2 ^ ((-7 : ℝ) / 6) * Real.log 2 ^ ((7 : ℝ) / 6) := hone7.symm
      _ ≤ Real.log 2 ^ ((-7 : ℝ) / 6) *
            ((B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) ^ ((1 : ℝ) / 6)
              * (Real.sqrt (N : ℝ) * B)) := mul_le_mul_of_nonneg_left hroot hcl.le
      _ = (Real.log 2 ^ ((-7 : ℝ) / 6) *
            (B ^ 2 * Real.log ((p : ℝ) * (N : ℝ)) ^ 7 / (N : ℝ)) ^ ((1 : ℝ) / 6))
              * (Real.sqrt (N : ℝ) * B) := (mul_assoc _ _ _).symm
  have hkey_n :
      1 / (Real.sqrt (n : ℝ) * B)
        ≤ Real.log 2 ^ ((-7 : ℝ) / 6) *
            (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) :=
    hkeygen n hn hn1
  have hkey_m :
      1 / (Real.sqrt (m : ℝ) * B)
        ≤ Real.log 2 ^ ((-7 : ℝ) / 6) *
            (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) :=
    hkeygen m hm hm1
  have hMn_num :
      CM / kap ^ 3 / (Real.sqrt (n : ℝ) * B)
        ≤ (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) *
            (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) := by
    have hcnpos : (0 : ℝ) < CM / kap ^ 3 := div_pos hCM (pow_pos hkap 3)
    calc CM / kap ^ 3 / (Real.sqrt (n : ℝ) * B)
        = CM / kap ^ 3 * (1 / (Real.sqrt (n : ℝ) * B)) := by rw [div_eq_mul_inv, one_div]
      _ ≤ CM / kap ^ 3 * (Real.log 2 ^ ((-7 : ℝ) / 6) *
            (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left hkey_n hcnpos.le
      _ = (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) *
            (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) := by
        exact (mul_assoc _ _ _).symm
  have hMm_num :
      CM / kap ^ 3 / (Real.sqrt (m : ℝ) * B)
        ≤ (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) *
            (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) := by
    have hcnpos : (0 : ℝ) < CM / kap ^ 3 := div_pos hCM (pow_pos hkap 3)
    calc CM / kap ^ 3 / (Real.sqrt (m : ℝ) * B)
        = CM / kap ^ 3 * (1 / (Real.sqrt (m : ℝ) * B)) := by
          rw [div_eq_mul_inv, one_div]
      _ ≤ CM / kap ^ 3 * (Real.log 2 ^ ((-7 : ℝ) / 6) *
            (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left hkey_m hcnpos.le
      _ = (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) *
            (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) := by
        exact (mul_assoc _ _ _).symm
  have hkeyE : ∀ (x a b c : ℝ), (x / a) / (b * c) = (x / b) / (a * c) := by
    intro x a b c
    rw [div_div, div_div, mul_left_comm]
  have hMnterm : Mnv / (kap ^ 3 * B) ≤
      (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) *
        (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) := by
    have h2 : Mnv / (kap ^ 3 * B) ≤ (CM / Real.sqrt (n : ℝ)) / (kap ^ 3 * B) := by
      rw [div_le_div_iff₀ hLbar_pos hLbar_pos]
      exact mul_le_mul_of_nonneg_right hMn_le hLbar_pos.le
    refine le_trans h2 ?_
    rw [hkeyE CM (Real.sqrt (n : ℝ)) (kap ^ 3) B]
    exact hMn_num
  have hMmterm : Mmv / (kap ^ 3 * B) ≤
      (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) *
        (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) := by
    have h2 : Mmv / (kap ^ 3 * B) ≤ (CM / Real.sqrt (m : ℝ)) / (kap ^ 3 * B) := by
      rw [div_le_div_iff₀ hLbar_pos hLbar_pos]
      exact mul_le_mul_of_nonneg_right hMm_le hLbar_pos.le
    refine le_trans h2 ?_
    rw [hkeyE CM (Real.sqrt (m : ℝ)) (kap ^ 3) B]
    exact hMm_num
  have hsum4 := add_le_add (add_le_add (add_le_add ht1_le hMnterm) ht3_le) hMmterm
  set Mx : ℝ := max (kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6))
      (δ1 * kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) with hMxdef
  set Pn : ℝ := (B ^ 2 * Real.log ((p : ℝ) * (n : ℝ)) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6) with hPndef
  set Pm : ℝ := (B ^ 2 * Real.log ((p : ℝ) * (m : ℝ)) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6) with hPmdef
  have hcomb :
      kap * Pn + (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) * Pn
          + δ1 * kap * Pm + (CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) * Pm
        = (kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) * Pn
          + (δ1 * kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) * Pm := by
    rw [add_mul, add_mul]
    ac_rfl
  have hMx :
      (kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) * Pn
          + (δ1 * kap + CM / kap ^ 3 * Real.log 2 ^ ((-7 : ℝ) / 6)) * Pm
        ≤ Mx * (Pn + Pm) := by
    rw [hMxdef, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hQn_nonneg)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hQm_nonneg)
  have hinner := le_trans hsum4 (le_trans (le_of_eq hcomb) hMx)
  have hfin : K2 * (Mx * (Pn + Pm)) ≤ (K2 * Mx + 1) * (Pn + Pm) := by
    have hS := add_nonneg hQn_nonneg hQm_nonneg
    rw [← mul_assoc, add_mul, one_mul]
    exact le_add_of_nonneg_right hS
  exact le_trans hbridge
    (le_trans hρ (le_trans (mul_le_mul_of_nonneg_left hinner hK2_pos.le) hfin))
  /- @proof-region region.root.38d5f2c27e39 end -/

theorem Theorem_1_two_sample_Gaussian_approximation_over_rectangles_rho_n_m_double_star_bound :
    ∀ (δ1 δ2 : ℝ), 0 < δ2 → δ2 < δ1 →
      ∃ K3 : ℝ, 0 < K3 ∧ ∃ b : ℝ, 0 < b ∧ ∃ c1 : ℝ, 0 < c1 ∧
        ∀ (δ : ℕ → ℕ → ℝ),
          (∀ (n m : ℕ), 0 < n → 0 < m → δ2 < |δ n m| ∧ |δ n m| < δ1) →
          ∀ (n : ℕ), 0 < n → ∀ (m : ℕ), 0 < m → ∀ (p : ℕ), 2 ≤ p →
            ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (μX μY : Fin p → ℝ)
              (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
              (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ),
              (∀ i, Measurable (X i)) →
              (∀ i, Measurable (Y i)) →
              (∀ i, Measurable (F i)) →
              (∀ i, Measurable (G i)) →
              iIndepFun (fun i => jointFamily X Y F G i) P →
              (∀ i j, Integrable (fun ω => X i ω j) P) →
              (∀ i j, ∫ ω, X i ω j ∂P = μX j) →
              (∀ i j, Integrable (fun ω => Y i ω j) P) →
              (∀ i j, ∫ ω, Y i ω j ∂P = μY j) →
              (∀ i j k, Integrable (fun ω => (X i ω j - μX j) * (X i ω k - μX k)) P) →
              (∀ i j k, Integrable (fun ω => (Y i ω j - μY j) * (Y i ω k - μY k)) P) →
              (∀ i j, Integrable (fun ω => |X i ω j - μX j| ^ 3) P) →
              (∀ i j, Integrable (fun ω => |Y i ω j - μY j| ^ 3) P) →
              (∀ i, IsCenteredGaussianVector P (fun ω j => F i ω j - μX j)
                (fun j k => ∫ ω, (X i ω j - μX j) * (X i ω k - μX k) ∂P)) →
              (∀ i, IsCenteredGaussianVector P (fun ω j => G i ω j - μY j)
                (fun j k => ∫ ω, (Y i ω j - μY j) * (Y i ω k - μY k) ∂P)) →
              (∀ j, Integrable
                (fun ω => (combinedStat n m (δ n m) μX μY X Y ω j) ^ 2) P) →
              (∀ j, b ≤ ∫ ω, (combinedStat n m (δ n m) μX μY X Y ω j) ^ 2 ∂P) →
                          ∀ (B : ℝ), 1 ≤ B →
                            LThird P X μX ≤ B →
                            LThird P Y μY ≤ B →
                            (∀ i j, Integrable (fun ω => Real.exp (|X i ω j - μX j| / B)) P) →
                            (∀ i j, ∫ ω, Real.exp (|X i ω j - μX j| / B) ∂P ≤ 2) →
                            (∀ i j, Integrable (fun ω => Real.exp (|Y i ω j - μY j| / B)) P) →
                            (∀ i j, ∫ ω, Real.exp (|Y i ω j - μY j| / B) ∂P ≤ 2) →
                            B ^ 2 * (Real.log ((p : ℝ) * (n : ℝ))) ^ 7 / (n : ℝ) ≤ c1 →
                            B ^ 2 * (Real.log ((p : ℝ) * (m : ℝ))) ^ 7 / (m : ℝ) ≤ c1 →
                            rhoStarStar P (combinedStat n m (δ n m) μX μY X Y)
                                (combinedStat n m (δ n m) μX μY F G)
                              ≤ K3 * ((B ^ 2 * (Real.log ((p : ℝ) * (n : ℝ))) ^ 7 / (n : ℝ)) ^ ((1 : ℝ) / 6)
                                  + (B ^ 2 * (Real.log ((p : ℝ) * (m : ℝ))) ^ 7 / (m : ℝ)) ^ ((1 : ℝ) / 6))
 := by
  intro δ1 δ2 hδ2 hδ21
  obtain ⟨K3, hK3, c1, hc1, h⟩ :=
    Theorem_1_two_sample_Gaussian_approximation_over_rectangles_rho_n_m_double_star_bound_uniform_variance δ1 δ2 1 hδ2 hδ21 one_pos
  exact ⟨K3, hK3, 1, one_pos, c1, hc1, h⟩

end Statlib.Imported

-- Paper root revision 47a12f4f-6abe-4556-a786-38a8b04242f8

