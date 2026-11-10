import Statlib.StatFoundation.Convergence.AnalysisTools.ConvergenceModes
import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2663820550_efe405d1_5ed6be9e
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.ProvedNodes.Node_2941214830_746485b7_90d29598

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
theorem statopia_math_node_1921948430_865bfebf : ∀ (Ω : Type*) [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : ℕ → Ω → ℝ) (rho : Ω → ℝ≥0∞) (C : ℝ)
    (hmeas : ∀ n : ℕ, @Measurable Ω ℝ m0 inferInstance (h n))
    (hnonneg : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ h n ω)
    (hint : ∀ n : ℕ, Integrable (fun ω => (h n ω) ^ 2) μ)
    (hdiff : ∀ m n : ℕ, n ≤ m →
      ∫ ω, (h m ω - h n ω) ^ 2 ∂μ
        = (∫ ω, (h m ω) ^ 2 ∂μ) - ∫ ω, (h n ω) ^ 2 ∂μ)
    (hmom : Filter.Tendsto (fun n : ℕ => ∫ ω, (h n ω) ^ 2 ∂μ) Filter.atTop (𝓝 C))
    (haeconv : ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (h n ω)) Filter.atTop (𝓝 (rho ω))), ∃ g : Ω → ℝ,
        (∀ᵐ ω ∂μ, 0 ≤ g ω) ∧
        (∀ᵐ ω ∂μ, rho ω = ENNReal.ofReal (g ω)) ∧
        Integrable (fun ω => (g ω) ^ 2) μ ∧
        (∫ ω, (g ω) ^ 2 ∂μ = C) := by
  /- @proof-region region.target-node.session.988ce66336e8e28b begin -/
  intro Ω m0 μ _ h rho C hmeas hnonneg hint hdiff hmom haeconv
  classical
  have hnn_all : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 ≤ h n ω := MeasureTheory.ae_all_iff.2 hnonneg
  set a : ℕ → ℝ := fun n => ∫ ω, (h n ω) ^ 2 ∂μ with ha_def
  have hmom' : Tendsto a atTop (𝓝 C) := hmom
  have ha_mono : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hd : ∫ ω, (h (n + 1) ω - h n ω) ^ 2 ∂μ = a (n + 1) - a n :=
      hdiff (n + 1) n (Nat.le_succ n)
    have hnn : 0 ≤ ∫ ω, (h (n + 1) ω - h n ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg (h (n + 1) ω - h n ω))
    linarith
  have ha_le : ∀ n, a n ≤ C := by
    intro n
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hmom'
      (eventually_atTop.2 ⟨n, fun m hm => ha_mono hm⟩)
  have hex : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ C - a n ≤ (1 / 4 : ℝ) ^ (k + 1) := by
    intro k
    have hlt : C - (1 / 4 : ℝ) ^ (k + 1) < C := by
      have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ (k + 1) := by positivity
      linarith
    have hev : ∀ᶠ n in atTop, a n ∈ Set.Ioi (C - (1 / 4 : ℝ) ^ (k + 1)) :=
      hmom' (isOpen_Ioi.mem_nhds hlt)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
    refine ⟨max n₀ k, le_max_right _ _, ?_⟩
    have hmem : a (max n₀ k) ∈ Set.Ioi (C - (1 / 4 : ℝ) ^ (k + 1)) := hn₀ _ (le_max_left _ _)
    simp only [Set.mem_Ioi] at hmem
    linarith
  let N : ℕ → ℕ := fun k => Nat.find (hex k)
  have hNspec : ∀ k, k ≤ N k ∧ C - a (N k) ≤ (1 / 4 : ℝ) ^ (k + 1) :=
    fun k => Nat.find_spec (hex k)
  have hNmono : Monotone N := by
    refine monotone_nat_of_le_succ (fun k => ?_)
    have hp : (fun n => k ≤ n ∧ C - a n ≤ (1 / 4 : ℝ) ^ (k + 1)) (N (k + 1)) := by
      refine ⟨le_trans (Nat.le_succ k) (hNspec (k + 1)).1, ?_⟩
      refine le_trans (hNspec (k + 1)).2 ?_
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact Nat.find_le hp
  have hNtend : Tendsto N atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun p hp => le_trans hp (hNspec p).1⟩)
  have hbound : ∀ k l : ℕ, k ≤ l →
      (∫ ω, (h (N l) ω - h (N k) ω) ^ 2 ∂μ) ≤ (1 / 4 : ℝ) ^ (k + 1) := by
    intro k l hkl
    have hd : ∫ ω, (h (N l) ω - h (N k) ω) ^ 2 ∂μ = a (N l) - a (N k) :=
      hdiff (N l) (N k) (hNmono hkl)
    have h1 : a (N l) ≤ C := ha_le (N l)
    have h2 : C - a (N k) ≤ (1 / 4 : ℝ) ^ (k + 1) := (hNspec k).2
    linarith
  have hbound' : ∀ K n m : ℕ, K ≤ n → K ≤ m →
      (∫ ω, (h (N n) ω - h (N m) ω) ^ 2 ∂μ) ≤ (1 / 4 : ℝ) ^ (K + 1) := by
    intro K n m hn hm
    have hpow : ∀ u v : ℕ, u ≤ v → (1 / 4 : ℝ) ^ (v + 1) ≤ (1 / 4 : ℝ) ^ (u + 1) :=
      fun u v huv => pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rcases le_total n m with hnm | hnm
    · have h1 : ∫ ω, (h (N m) ω - h (N n) ω) ^ 2 ∂μ ≤ (1 / 4 : ℝ) ^ (n + 1) :=
        hbound n m hnm
      have h3 : ∫ ω, (h (N n) ω - h (N m) ω) ^ 2 ∂μ
          = ∫ ω, (h (N m) ω - h (N n) ω) ^ 2 ∂μ := by
        refine integral_congr_ae (Eventually.of_forall (fun ω => ?_))
        ring
      have h2 : (1 / 4 : ℝ) ^ (n + 1) ≤ (1 / 4 : ℝ) ^ (K + 1) := hpow K n hn
      rw [h3]
      linarith
    · have h1 : ∫ ω, (h (N n) ω - h (N m) ω) ^ 2 ∂μ ≤ (1 / 4 : ℝ) ^ (m + 1) :=
        hbound m n hnm
      have h2 : (1 / 4 : ℝ) ^ (m + 1) ≤ (1 / 4 : ℝ) ^ (K + 1) := hpow K m hm
      linarith
  have hAESM : ∀ k : ℕ, AEStronglyMeasurable (h (N k)) μ :=
    fun k => (hmeas (N k)).aestronglyMeasurable
  have hmemLp : ∀ k : ℕ, MemLp (h (N k)) 2 μ := fun k =>
    (MeasureTheory.memLp_two_iff_integrable_sq (hAESM k)).2 (hint (N k))
  have hnorm_eq : ∀ x : ℝ, ‖x‖ ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hcauchy : ∀ K n m : ℕ, K ≤ n → K ≤ m →
      eLpNorm (fun ω => h (N n) ω - h (N m) ω) 2 μ < ENNReal.ofReal ((1 / 2 : ℝ) ^ K) := by
    intro K n m hn hm
    have hmem : MemLp (fun ω => h (N n) ω - h (N m) ω) 2 μ :=
      (hmemLp n).sub (hmemLp m)
    have hI : ∫ ω, (h (N n) ω - h (N m) ω) ^ 2 ∂μ ≤ (1 / 4 : ℝ) ^ (K + 1) :=
      hbound' K n m hn hm
    have hsq_eq : ∫ ω, ‖h (N n) ω - h (N m) ω‖ ^ (2 : ℝ) ∂μ
        = ∫ ω, (h (N n) ω - h (N m) ω) ^ 2 ∂μ := by
      refine integral_congr_ae (Eventually.of_forall (fun ω => ?_))
      exact hnorm_eq _
    have hsq : ∫ ω, ‖h (N n) ω - h (N m) ω‖ ^ (2 : ℝ) ∂μ ≤ (1 / 4 : ℝ) ^ (K + 1) := by
      rw [hsq_eq]
      exact hI
    have hkey : (1 / 4 : ℝ) ^ (K + 1) = ((1 / 2 : ℝ) ^ (K + 1)) ^ 2 := by
      rw [← pow_mul, show (K + 1) * 2 = 2 * (K + 1) from by ring, pow_mul]
      norm_num
    have hs : Real.sqrt (∫ ω, ‖h (N n) ω - h (N m) ω‖ ^ (2 : ℝ) ∂μ) ≤ (1 / 2 : ℝ) ^ (K + 1) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (K + 1)), ← hkey]
      exact Real.sqrt_le_sqrt hsq
    have hA : (∫ ω, ‖h (N n) ω - h (N m) ω‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹)
        ≤ (1 / 2 : ℝ) ^ (K + 1) := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 from by norm_num, ← Real.sqrt_eq_rpow]
      exact hs
    rw [MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hmem,
      show (2 : ℝ≥0∞).toReal = 2 from by simp]
    rw [ENNReal.ofReal_lt_ofReal_iff']
    refine ⟨lt_of_le_of_lt hA ?_, by positivity⟩
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) K]
  have hB : ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≠ ⊤ := by
    have hsumm : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h1 : ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k)
        = ENNReal.ofReal (∑' k : ℕ, (1 / 2 : ℝ) ^ k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm]
    rw [h1]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ ω ∂μ, ∃ x, Tendsto (fun k => h (N k) ω) atTop (𝓝 x) :=
    Statlib.StatFoundation.Convergence.ae_tendsto_of_cauchy_eLpNorm hAESM (by norm_num) hB hcauchy
  let g : Ω → ℝ := fun ω =>
    if hh : ∃ x, Tendsto (fun k => h (N k) ω) atTop (𝓝 x) then Classical.choose hh else 0
  have hg_tend : ∀ᵐ ω ∂μ, Tendsto (fun k => h (N k) ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae] with ω hω
    dsimp only [g]
    rw [dif_pos hω]
    exact Classical.choose_spec hω
  have heLp : Tendsto (fun k => eLpNorm (fun ω => h (N k) ω - g ω) 2 μ) atTop (𝓝 0) :=
    Statlib.StatFoundation.Convergence.tendsto_eLpNorm_of_cauchy_tendsto_ae hAESM g hB hcauchy
      hg_tend
  have hg_nonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω := by
    filter_upwards [hnn_all, hg_tend] with ω hn hg
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hg (Eventually.of_forall (fun k => hn (N k)))
  have hg_eq : ∀ᵐ ω ∂μ, rho ω = ENNReal.ofReal (g ω) := by
    filter_upwards [haeconv, hg_tend] with ω hconv hg
    have h1 : Tendsto (fun k => ENNReal.ofReal (h (N k) ω)) atTop (𝓝 (rho ω)) :=
      hconv.comp hNtend
    have h2 : Tendsto (fun k => ENNReal.ofReal (h (N k) ω)) atTop (𝓝 (ENNReal.ofReal (g ω))) :=
      ENNReal.tendsto_ofReal hg
    exact tendsto_nhds_unique h1 h2
  have hAESg : AEStronglyMeasurable g μ :=
    statopia_math_node_2663820550_efe405d1 Ω μ (fun k => h (N k)) g hAESM hg_tend
  have hMemLpg : MemLp g 2 μ :=
    Statlib.StatFoundation.Convergence.memLp_of_cauchy_tendsto (p := 2) (by norm_num) hmemLp g
      hAESg heLp
  have hIntg : Integrable (fun ω => (g ω) ^ 2) μ := hMemLpg.integrable_sq
  have haN : Tendsto (fun k => ∫ ω, (h (N k) ω) ^ 2 ∂μ) atTop (𝓝 C) := hmom'.comp hNtend
  refine ⟨g, hg_nonneg, hg_eq, hIntg, ?_⟩
  exact statopia_math_node_2941214830_746485b7 Ω μ (fun k => h (N k)) g C hmemLp hMemLpg heLp haN
  /- @proof-region region.target-node.session.988ce66336e8e28b end -/

end Statlib.Imported
end

