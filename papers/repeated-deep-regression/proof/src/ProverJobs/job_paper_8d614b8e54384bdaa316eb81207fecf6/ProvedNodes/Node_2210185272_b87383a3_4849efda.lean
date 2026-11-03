import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_1390765457_210d1e15_5d8f5653
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_2130039367_ac22ae17_25b6ec44

namespace PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6


open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open _root_.PaperProofTasks.job_paper_8d614b8e54384bdaa316eb81207fecf6.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
noncomputable section
set_option maxHeartbeats 1000000

set_option autoImplicit false in
theorem statopia_math_node_2210185272_b87383a3 : ∀ (B1 : ℝ) (hB1 : 0 < B1)
    {Ωs : Type*} [MeasurableSpace Ωs]
    (PX : Measure Ωs) [IsProbabilityMeasure PX]
    (f0 : Ωs → ℝ) (F : Set (Ωs → ℝ))
    (hf0_meas : Measurable f0)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hf0_bound : ∀ x : Ωs, |f0 x| ≤ B1)
    (hF_bound : ∀ f ∈ F, ∀ x : Ωs, |f x| ≤ B1)
    (hF_int : ∀ f ∈ F, Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX)
    {Ωrand : Type*} [MeasurableSpace Ωrand]
    (P : Measure Ωrand) [IsProbabilityMeasure P]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n → Fin m → Ωrand → Ωs)
    (hX_meas : ∀ p : Fin n × Fin m, Measurable (X p.1 p.2))
    (sigma : Fin n → Fin m → Ωrand → ℝ)
    (hsigma_meas : ∀ p : Fin n × Fin m, Measurable (sigma p.1 p.2))
    (hsigma_law : ∀ p : Fin n × Fin m, Measure.map (sigma p.1 p.2) P = rademacherLaw)
    (hsigma_indep : iIndepFun (fun p : Fin n × Fin m => sigma p.1 p.2) P)
    (hsigma_indep_X : IndepFun (fun ω => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
      (fun ω => fun p : Fin n × Fin m => X p.1 p.2 ω) P)
    (phi : ℝ → ℝ) (rstar : ℝ)
    (hfix : IsRademacherFixedPoint F PX f0 X sigma P phi rstar)
    (r : ℝ) (hr : rstar ≤ r)
    (Fs : Finset (Ωs → ℝ)) (hFs : (Fs : Set (Ωs → ℝ)) ⊆ F),
    (∫ ω, sSup ((fun f : Ωs → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 /
            (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P)
      ≤ 40 * B1 * phi r / r := by
  /- @proof-region region.target-node.session.7702e9e901e81608 begin -/
  intro B1 hB1 Ωs mΩs PX hPX f0 F hf0_meas hF_meas hf0_bound hF_bound hF_int
  intro Ωrand mΩrand P hP n m hn hm X hX_meas sigma hsigma_meas hsigma_law hsigma_indep hsigma_indep_X
  intro phi rstar hfix r hr Fs hFs
  have hrstar : 0 < rstar := hfix.1
  have hrpos : 0 < r := hrstar.trans_le hr
  have hsub : IsSubRootOn phi (Set.Ici rstar) := hfix.2.1
  have hφr : 0 ≤ phi r := by
    have h1 : 0 ≤ phi r / Real.sqrt r := hsub.1 r hr
    have h2 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have h3 : 0 ≤ phi r / Real.sqrt r * Real.sqrt r := mul_nonneg h1 h2.le
    rwa [div_mul_cancel₀ _ h2.ne'] at h3
  have hlin : ∀ f ∈ F, ∀ x : Ωs, |f x - f0 x| ≤ 2 * B1 := by
    intro f hf x
    have h1 := abs_le.mp (hF_bound f hf x)
    have h2 := abs_le.mp (hf0_bound x)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hquad : ∀ f ∈ Fs, ∀ x : Ωs, 0 ≤ (f x - f0 x) ^ 2 ∧ (f x - f0 x) ^ 2 ≤ 4 * B1 ^ 2 := by
    intro f hf x
    have hb := abs_le.mp (hlin f (hFs hf) x)
    have h2 : (f x - f0 x) ^ 2 ≤ (2 * B1) ^ 2 := by
      nlinarith [sq_nonneg (f x - f0 x), sq_nonneg (2 * B1 - (f x - f0 x)),
        sq_nonneg (2 * B1 + (f x - f0 x))]
    have h3 : (2 * B1) ^ 2 = 4 * B1 ^ 2 := by ring
    exact ⟨sq_nonneg _, by linarith [h2, h3]⟩
  have hA : ∀ f ∈ Fs, 0 ≤ predError PX f0 f ∧ predError PX f0 f ≤ 4 * B1 ^ 2 := by
    intro f hf
    have h1 : 0 ≤ predError PX f0 f := by
      have h := MeasureTheory.integral_mono_of_nonneg (μ := PX)
        (f := fun _ => (0 : ℝ)) (g := fun x => (f x - f0 x) ^ 2)
        (Filter.Eventually.of_forall (fun _ => le_refl (0 : ℝ)))
        (hF_int f (hFs hf))
        (Filter.Eventually.of_forall (fun x => (hquad f hf x).1))
      simpa using h
    have h2 : predError PX f0 f ≤ 4 * B1 ^ 2 := by
      have h := MeasureTheory.integral_mono_of_nonneg (μ := PX)
        (f := fun x => (f x - f0 x) ^ 2) (g := fun _ => 4 * B1 ^ 2)
        (Filter.Eventually.of_forall (fun x => (hquad f hf x).1))
        (integrable_const (4 * B1 ^ 2))
        (Filter.Eventually.of_forall (fun x => (hquad f hf x).2))
      simpa using h
    exact ⟨h1, h2⟩
  classical
  have hNpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
    have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    exact mul_pos h1 h2
  have hone : ∀ k : ℕ, (1 : ℝ) ≤ (4 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ j ih => rw [pow_succ]; nlinarith [ih]
  have hpow_ge : ∀ k : ℕ, (k : ℝ) ≤ (4 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ j := hone j
        have h5 : (4 : ℝ) ^ (j + 1) = (4 : ℝ) ^ j * 4 := pow_succ 4 j
        push_cast
        nlinarith [ih, h4, h5]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 4 * B1 ^ 2 ≤ (4 : ℝ) ^ K * r := by
    obtain ⟨K, hK⟩ := exists_nat_ge (max ((4 * B1 ^ 2) / r) 1)
    refine ⟨K, ?_⟩
    have h1 : (4 * B1 ^ 2) / r ≤ (K : ℝ) := le_trans (le_max_left _ _) hK
    have h2 : (4 * B1 ^ 2) / r * r = 4 * B1 ^ 2 := div_mul_cancel₀ _ hrpos.ne'
    calc 4 * B1 ^ 2 = (4 * B1 ^ 2) / r * r := by rw [h2]
      _ ≤ (K : ℝ) * r := mul_le_mul_of_nonneg_right h1 hrpos.le
      _ ≤ (4 : ℝ) ^ K * r := mul_le_mul_of_nonneg_right (hpow_ge K) hrpos.le
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Finset (Ωs → ℝ),
      T = fun k => Fs.filter (fun g => predError PX f0 g ≤ (4 : ℝ) ^ k * r) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ,
      w = fun k => if k = 0 then r⁻¹ else (((4 : ℝ) ^ (k - 1) + 1) * r)⁻¹ := ⟨_, rfl⟩
  obtain ⟨QSq, hQ⟩ : ∃ QSq : ℕ → Ωrand → ℝ, QSq = fun k ω => sSup ((fun f : Ωs → ℝ =>
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) '' ((T k) : Set (Ωs → ℝ))) :=
    ⟨_, rfl⟩
  obtain ⟨Sq, hS⟩ : ∃ Sq : ℕ → Ωrand → ℝ,
      Sq = fun k ω => rademacherFiniteSup X f0 sigma ω (T k) := ⟨_, rfl⟩
  have hsupp : ∀ᵐ y ∂rademacherLaw, |y| = 1 := by
    rw [MeasureTheory.ae_iff]
    simp [rademacherLaw, Measure.dirac_apply]
  have hσp : ∀ p : Fin n × Fin m, ∀ᵐ ω ∂P, |sigma p.1 p.2 ω| = 1 := by
    intro p
    have hms : MeasurableSet {y : ℝ | |y| = 1} :=
      (isClosed_eq continuous_abs continuous_const).measurableSet
    have h1 := hsupp
    rw [← hsigma_law p] at h1
    exact (MeasureTheory.ae_map_iff (hsigma_meas p).aemeasurable hms).mp h1
  have hσall : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin m, |sigma p.1 p.2 ω| = 1 := by
    have key : ∀ s : Finset (Fin n × Fin m), ∀ᵐ ω ∂P, ∀ p ∈ s, |sigma p.1 p.2 ω| = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          filter_upwards [ih, hσp a] with ω h1 h2
          intro p hp
          rcases Finset.mem_insert.mp hp with rfl | h
          · exact h2
          · exact h1 p h
    simpa using key Finset.univ
  have hw0 : w 0 = r⁻¹ := by
    simp only [hw]; simp
  have hwsucc : ∀ j : ℕ, w (j + 1) = (((4 : ℝ) ^ j + 1) * r)⁻¹ := by
    intro j
    simp only [hw]; simp
  have hwnonneg : ∀ k, 0 ≤ w k := by
    intro k
    simp only [hw]
    split_ifs with hk
    · positivity
    · positivity
  have hTmem : ∀ (k : ℕ) (g : Ωs → ℝ),
      g ∈ T k ↔ (g ∈ Fs ∧ predError PX f0 g ≤ (4 : ℝ) ^ k * r) := by
    intro k g
    simp only [hT, Finset.mem_filter]
  have hQval : ∀ (k : ℕ) (ω : Ωrand), QSq k ω = sSup ((fun f : Ωs → ℝ =>
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) '' ((T k) : Set (Ωs → ℝ))) := by
    intro k ω
    simp only [hQ]
  have hSval : ∀ (k : ℕ) (ω : Ωrand), Sq k ω = sSup ((fun f : Ωs → ℝ =>
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω))|) '' ((T k) : Set (Ωs → ℝ))) := by
    intro k ω
    simp only [hS, rademacherFiniteSup]
  have hsup_nonneg : ∀ (G : Finset (Ωs → ℝ)) (g : (Ωs → ℝ) → Ωrand → ℝ),
      (∀ f ∈ G, ∀ ω, 0 ≤ g f ω) → ∀ ω, 0 ≤ sSup ((fun f => g f ω) '' (G : Set (Ωs → ℝ))) := by
    intro G g hg ω
    rcases Finset.eq_empty_or_nonempty G with he | hne
    · rw [he]; simp
    · obtain ⟨f, hf⟩ := hne
      have hbdd : BddAbove ((fun f => g f ω) '' (G : Set (Ωs → ℝ))) := by
        refine ⟨∑ f' ∈ G, |g f' ω|, ?_⟩
        rintro x ⟨f', hf', rfl⟩
        calc g f' ω = |g f' ω| := (abs_of_nonneg (hg f' hf' ω)).symm
          _ ≤ ∑ f'' ∈ G, |g f'' ω| :=
            Finset.single_le_sum (f := fun i => |g i ω|) (fun i _ => abs_nonneg _) hf'
      exact le_trans (hg f hf ω) (le_csSup hbdd ⟨f, hf, rfl⟩)
  have hQSq_nonneg : ∀ k ω, 0 ≤ QSq k ω := by
    intro k ω
    rw [hQval k ω]
    exact hsup_nonneg (T k) (fun f ω => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
      sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) (fun f _ _ => abs_nonneg _) ω
  have hSq_nonneg : ∀ k ω, 0 ≤ Sq k ω := by
    intro k ω
    rw [hSval k ω]
    exact hsup_nonneg (T k) (fun f ω => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
      sigma i j ω * (f (X i j ω) - f0 (X i j ω))|) (fun f _ _ => abs_nonneg _) ω
  have hQSq_bound : ∀ k : ℕ, ∀ᵐ ω ∂P, QSq k ω ≤ 4 * B1 ^ 2 := by
    intro k
    filter_upwards [hσall] with ω hω
    rw [hQval k ω]
    refine Real.sSup_le ?_ (by positivity)
    rintro x ⟨f, hf, rfl⟩
    have hfFs : f ∈ Fs := ((hTmem k f).mp hf).1
    have hsum : |∑ i : Fin n, ∑ j : Fin m, sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|
        ≤ (n : ℝ) * (m : ℝ) * (4 * B1 ^ 2) := by
      calc |∑ i : Fin n, ∑ j : Fin m, sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|
          ≤ ∑ i : Fin n, |∑ j : Fin m, sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin m, |sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ i : Fin n, ∑ j : Fin m, |sigma i j ω| * |(f (X i j ω) - f0 (X i j ω)) ^ 2| := by
            simp [abs_mul]
        _ ≤ ∑ i : Fin n, ∑ j : Fin m, 1 * (4 * B1 ^ 2) := by
            refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
            have h1 : |sigma i j ω| = 1 := hω (i, j)
            have h2 : |(f (X i j ω) - f0 (X i j ω)) ^ 2| ≤ 4 * B1 ^ 2 := by
              rw [abs_of_nonneg (hquad f hfFs (X i j ω)).1]
              exact (hquad f hfFs (X i j ω)).2
            simp only [h1, one_mul]
            exact h2
        _ = (n : ℝ) * (m : ℝ) * (4 * B1 ^ 2) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|
        = ((n : ℝ) * (m : ℝ))⁻¹ * |∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2| := by
          rw [abs_mul, abs_inv, abs_of_pos hNpos]
      _ ≤ ((n : ℝ) * (m : ℝ))⁻¹ * ((n : ℝ) * (m : ℝ) * (4 * B1 ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hNpos))
      _ = 4 * B1 ^ 2 := by
          rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
  have hrad_bound : ∀ (G : Finset (Ωs → ℝ)), (G : Set (Ωs → ℝ)) ⊆ F →
      ∀ᵐ ω ∂P, rademacherFiniteSup X f0 sigma ω G ≤ 2 * B1 := by
    intro G hG
    filter_upwards [hσall] with ω hω
    refine Real.sSup_le ?_ (by positivity)
    rintro x ⟨f, hf, rfl⟩
    have hsum : |∑ i : Fin n, ∑ j : Fin m, sigma i j ω * (f (X i j ω) - f0 (X i j ω))|
        ≤ (n : ℝ) * (m : ℝ) * (2 * B1) := by
      calc |∑ i : Fin n, ∑ j : Fin m, sigma i j ω * (f (X i j ω) - f0 (X i j ω))|
          ≤ ∑ i : Fin n, |∑ j : Fin m, sigma i j ω * (f (X i j ω) - f0 (X i j ω))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ∑ j : Fin m, |sigma i j ω * (f (X i j ω) - f0 (X i j ω))| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ i : Fin n, ∑ j : Fin m, |sigma i j ω| * |f (X i j ω) - f0 (X i j ω)| := by
            simp [abs_mul]
        _ ≤ ∑ i : Fin n, ∑ j : Fin m, 1 * (2 * B1) := by
            refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
            have h1 : |sigma i j ω| = 1 := hω (i, j)
            have h2 : |f (X i j ω) - f0 (X i j ω)| ≤ 2 * B1 := hlin f (hG hf) (X i j ω)
            simp only [h1, one_mul]
            exact h2
        _ = (n : ℝ) * (m : ℝ) * (2 * B1) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω))|
        = ((n : ℝ) * (m : ℝ))⁻¹ * |∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω))| := by
          rw [abs_mul, abs_inv, abs_of_pos hNpos]
      _ ≤ ((n : ℝ) * (m : ℝ))⁻¹ * ((n : ℝ) * (m : ℝ) * (2 * B1)) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hNpos))
      _ = 2 * B1 := by
          rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
  have hbdd_image : ∀ (G : Finset (Ωs → ℝ)) (g : (Ωs → ℝ) → Ωrand → ℝ) (ω : Ωrand),
      (∀ f ∈ G, 0 ≤ g f ω) → BddAbove ((fun f => g f ω) '' (G : Set (Ωs → ℝ))) := by
    intro G g ω hg
    refine ⟨∑ f' ∈ G, |g f' ω|, ?_⟩
    rintro x ⟨f', hf', rfl⟩
    calc g f' ω = |g f' ω| := (abs_of_nonneg (hg f' hf')).symm
      _ ≤ ∑ f'' ∈ G, |g f'' ω| :=
        Finset.single_le_sum (f := fun i => |g i ω|) (fun i _ => abs_nonneg _) hf'
  have hssup_insert : ∀ (G : Finset (Ωs → ℝ)) (g : (Ωs → ℝ) → Ωrand → ℝ) (ω : Ωrand)
      (c : Ωs → ℝ), c ∉ G → (∀ f ∈ G, 0 ≤ g f ω) → 0 ≤ g c ω →
      sSup ((fun f => g f ω) '' ((insert c G : Finset (Ωs → ℝ)) : Set (Ωs → ℝ)))
        = max (g c ω) (sSup ((fun f => g f ω) '' (G : Set (Ωs → ℝ)))) := by
    intro G g ω c hc hnn hc0
    have hbddG : BddAbove ((fun f => g f ω) '' (G : Set (Ωs → ℝ))) := by
      refine ⟨∑ f' ∈ G, |g f' ω|, ?_⟩
      rintro x ⟨f', hf', rfl⟩
      calc g f' ω = |g f' ω| := (abs_of_nonneg (hnn f' hf')).symm
        _ ≤ ∑ f'' ∈ G, |g f'' ω| :=
          Finset.single_le_sum (f := fun i => |g i ω|) (fun i _ => abs_nonneg _) hf'
    have hbddI : BddAbove ((fun f => g f ω) '' ((insert c G : Finset (Ωs → ℝ)) : Set (Ωs → ℝ))) := by
      refine ⟨max |g c ω| (∑ f' ∈ G, |g f' ω|), ?_⟩
      rintro x ⟨f', hf', rfl⟩
      rcases Finset.mem_insert.mp hf' with rfl | hmem
      · exact le_trans (le_abs_self _) (le_max_left _ _)
      · calc g f' ω = |g f' ω| := (abs_of_nonneg (hnn f' hmem)).symm
          _ ≤ ∑ f'' ∈ G, |g f'' ω| :=
            Finset.single_le_sum (f := fun i => |g i ω|) (fun i _ => abs_nonneg _) hmem
          _ ≤ max |g c ω| (∑ f'' ∈ G, |g f'' ω|) := le_max_right _ _
    refine le_antisymm ?_ ?_
    · refine Real.sSup_le ?_ ?_
      · rintro x ⟨f', hf', rfl⟩
        rcases Finset.mem_insert.mp hf' with rfl | hmem
        · exact le_max_left _ _
        · exact le_trans (le_csSup hbddG ⟨f', hmem, rfl⟩) (le_max_right _ _)
      · exact le_trans hc0 (le_max_left _ _)
    · refine max_le ?_ ?_
      · exact le_csSup hbddI ⟨c, Finset.mem_insert_self c G, rfl⟩
      · refine Real.sSup_le ?_ ?_
        · rintro x ⟨f', hf', rfl⟩
          exact le_csSup hbddI ⟨f', Finset.mem_insert_of_mem hf', rfl⟩
        · exact le_trans hc0 (le_csSup hbddI ⟨c, Finset.mem_insert_self c G, rfl⟩)
  have hsup_meas : ∀ (G : Finset (Ωs → ℝ)) (g : (Ωs → ℝ) → Ωrand → ℝ),
      (∀ f ∈ G, Measurable (g f)) → (∀ f ∈ G, ∀ ω, 0 ≤ g f ω) →
      Measurable (fun ω => sSup ((fun f => g f ω) '' (G : Set (Ωs → ℝ)))) := by
    intro G g
    induction G using Finset.induction_on with
    | empty =>
        intro _ _
        have h0 : (fun ω => sSup ((fun f => g f ω) '' ((∅ : Finset (Ωs → ℝ)) : Set (Ωs → ℝ))))
            = fun _ => (0 : ℝ) := by
          funext ω; simp
        rw [h0]; exact measurable_const
    | insert a s ha ih =>
        intro hg hnn
        have hga : Measurable (g a) := hg a (Finset.mem_insert_self a s)
        have hgs : Measurable (fun ω => sSup ((fun f => g f ω) '' (s : Set (Ωs → ℝ)))) :=
          ih (fun f hf => hg f (Finset.mem_insert_of_mem hf))
            (fun f hf => hnn f (Finset.mem_insert_of_mem hf))
        have heq : (fun ω => sSup ((fun f => g f ω) ''
              ((insert a s : Finset (Ωs → ℝ)) : Set (Ωs → ℝ))))
            = fun ω => max (g a ω) (sSup ((fun f => g f ω) '' (s : Set (Ωs → ℝ)))) := by
          funext ω
          exact hssup_insert s g ω a ha (fun f hf => hnn f (Finset.mem_insert_of_mem hf) ω)
            (hnn a (Finset.mem_insert_self a s) ω)
        rw [heq]
        exact hga.max hgs
  have hmeas_quad : ∀ (G : Finset (Ωs → ℝ)), (G : Set (Ωs → ℝ)) ⊆ F → ∀ f ∈ G,
      Measurable (fun ω => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) := by
    intro G hG f hf
    have hfm : Measurable f := hF_meas f (hG hf)
    have h1 : ∀ i j, Measurable (fun ω => f (X i j ω)) := fun i j => hfm.comp (hX_meas (i, j))
    have h2 : ∀ i j, Measurable (fun ω => f0 (X i j ω)) :=
      fun i j => hf0_meas.comp (hX_meas (i, j))
    have h3 : ∀ i j, Measurable (sigma i j) := fun i j => hsigma_meas (i, j)
    measurability
  have hQSq_meas : ∀ k, Measurable (QSq k) := by
    intro k
    have h1 : ∀ f ∈ T k, Measurable (fun ω => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) :=
      fun f hf => hmeas_quad (T k) (fun g hg => hFs ((hTmem k g).mp hg).1) f hf
    have h2 := hsup_meas (T k) (fun f ω => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) h1 (fun f _ _ => abs_nonneg _)
    have heq : (fun ω => sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) '' ((T k) : Set (Ωs → ℝ)))) = QSq k := by
      funext ω
      exact (hQval k ω).symm
    rw [← heq]
    exact h2
  have hQSq_int : ∀ k, Integrable (QSq k) P := by
    intro k
    refine Integrable.mono' (integrable_const (4 * B1 ^ 2)) (hQSq_meas k).aestronglyMeasurable ?_
    filter_upwards [hQSq_bound k] with ω hb
    have h1 : ‖QSq k ω‖ = QSq k ω := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQSq_nonneg k ω)]
    rw [h1]
    exact hb
  obtain ⟨Gf, hGf⟩ : ∃ Gf : (Ωs → ℝ) → Ωrand → ℝ, Gf = fun f ω =>
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 / (predError PX f0 f + r)| :=
    ⟨_, rfl⟩
  obtain ⟨Zf, hZf⟩ : ∃ Zf : Ωrand → ℝ,
      Zf = fun ω => sSup ((fun f : Ωs → ℝ => Gf f ω) '' (Fs : Set (Ωs → ℝ))) := ⟨_, rfl⟩
  obtain ⟨Rf, hRf⟩ : ∃ Rf : Ωrand → ℝ,
      Rf = fun ω => ∑ k ∈ Finset.range (K + 1), w k * QSq k ω := ⟨_, rfl⟩
  have hpoint : ∀ ω : Ωrand, Zf ω ≤ Rf ω := by
    intro ω
    rw [hZf, hRf]
    show sSup ((fun f : Ωs → ℝ => Gf f ω) '' (Fs : Set (Ωs → ℝ)))
      ≤ ∑ k ∈ Finset.range (K + 1), w k * QSq k ω
    refine Real.sSup_le ?_ ?_
    · rintro x ⟨f, hf, rfl⟩
      obtain ⟨Sv, hSv⟩ : ∃ Sv : ℝ, Sv = ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 / (predError PX f0 f + r) := ⟨_, rfl⟩
      have hGfval : Gf f ω = |((n : ℝ) * (m : ℝ))⁻¹ * Sv| := by
        rw [hGf]
        simp only [← hSv]
      show Gf f ω ≤ ∑ k ∈ Finset.range (K + 1), w k * QSq k ω
      rw [hGfval]
      obtain ⟨Un, hUn⟩ : ∃ Un : ℝ, Un = ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 := ⟨_, rfl⟩
      obtain ⟨av, hav⟩ : ∃ av : ℝ, av = predError PX f0 f := ⟨_, rfl⟩
      have hav0 : 0 ≤ av := by
        rw [hav]
        exact (hA f hf).1
      have hden : 0 < av + r := by linarith
      have hfac : Sv = Un / (av + r) := by
        rw [hSv, hUn, hav]
        simp only [Finset.sum_div]
      have hq : |((n : ℝ) * (m : ℝ))⁻¹ * Sv|
          = (av + r)⁻¹ * |((n : ℝ) * (m : ℝ))⁻¹ * Un| := by
        rw [hfac, div_eq_mul_inv, ← mul_assoc, abs_mul,
          abs_of_pos (inv_pos.mpr hden), mul_comm]
      have hhex : ∃ k : ℕ, predError PX f0 f ≤ (4 : ℝ) ^ k * r :=
        ⟨K, le_trans (hA f hf).2 hK⟩
      obtain ⟨mm, hmm⟩ : ∃ mm : ℕ, mm = Nat.find hhex := ⟨_, rfl⟩
      have hspec : predError PX f0 f ≤ (4 : ℝ) ^ mm * r := by
        rw [hmm]
        exact Nat.find_spec hhex
      have hmmK : mm ≤ K := by
        rw [hmm]
        exact Nat.find_min' hhex (le_trans (hA f hf).2 hK)
      have hmem : f ∈ T mm := (hTmem mm f).mpr ⟨hf, hspec⟩
      have hQv : |((n : ℝ) * (m : ℝ))⁻¹ * Un| ≤ QSq mm ω := by
        have hb : BddAbove ((fun g : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ *
            ∑ i : Fin n, ∑ j : Fin m,
              sigma i j ω * (g (X i j ω) - f0 (X i j ω)) ^ 2|) '' ((T mm) : Set (Ωs → ℝ))) :=
          hbdd_image (T mm) (fun g ω => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            sigma i j ω * (g (X i j ω) - f0 (X i j ω)) ^ 2|) ω (fun g _ => abs_nonneg _)
        have h1 : |((n : ℝ) * (m : ℝ))⁻¹ * Un| ≤ _ :=
          le_csSup hb ⟨f, hmem, by rw [hUn]⟩
        rwa [← hQval mm ω] at h1
      have hcoe : (av + r)⁻¹ ≤ w mm := by
        rcases Nat.eq_zero_or_pos mm with h0 | hpos
        · rw [h0, hw0]
          gcongr
          linarith
        · obtain ⟨kk, hkk⟩ : ∃ kk, mm = kk + 1 := ⟨mm - 1, by omega⟩
          rw [hkk, hwsucc kk]
          have hlt : (4 : ℝ) ^ kk * r < predError PX f0 f := by
            have h1 : ¬ (predError PX f0 f ≤ (4 : ℝ) ^ kk * r) := by
              intro hle
              have h2 : mm ≤ kk := by
                rw [hmm]
                exact Nat.find_min' hhex hle
              omega
            linarith
          have hpr : ((4 : ℝ) ^ kk + 1) * r ≤ av + r := by
            rw [hav]
            have hring : ((4 : ℝ) ^ kk + 1) * r = (4 : ℝ) ^ kk * r + r := by ring
            linarith
          gcongr
      calc |((n : ℝ) * (m : ℝ))⁻¹ * Sv|
          = (av + r)⁻¹ * |((n : ℝ) * (m : ℝ))⁻¹ * Un| := hq
        _ ≤ w mm * QSq mm ω := mul_le_mul hcoe hQv (abs_nonneg _) (hwnonneg _)
        _ ≤ ∑ k ∈ Finset.range (K + 1), w k * QSq k ω :=
            Finset.single_le_sum (f := fun k => w k * QSq k ω)
              (fun k _ => mul_nonneg (hwnonneg k) (hQSq_nonneg k ω))
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hmmK))
    · show (0 : ℝ) ≤ ∑ k ∈ Finset.range (K + 1), w k * QSq k ω
      refine Finset.sum_nonneg (fun k _ => ?_)
      exact mul_nonneg (hwnonneg k) (hQSq_nonneg k ω)
  have hband_all : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range (K + 1), QSq k ω ≤ 4 * B1 ^ 2 := by
    have key : ∀ s : Finset ℕ, ∀ᵐ ω ∂P, ∀ k ∈ s, QSq k ω ≤ 4 * B1 ^ 2 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          filter_upwards [ih, hQSq_bound a] with ω h1 h2
          intro k hk
          rcases Finset.mem_insert.mp hk with rfl | h
          · exact h2
          · exact h1 k h
    simpa using key (Finset.range (K + 1))
  have hIntR : Integrable Rf P := by
    have hCsum : (0 : ℝ) ≤ ∑ k ∈ Finset.range (K + 1), w k * (4 * B1 ^ 2) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hwnonneg k) (by positivity))
    have hmeas : AEStronglyMeasurable Rf P := by
      have key : ∀ s : Finset ℕ, Measurable (fun ω => ∑ k ∈ s, w k * QSq k ω) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using (measurable_const : Measurable fun _ : Ωrand => (0 : ℝ))
        | insert a s ha ih =>
            have hsu : (fun ω => ∑ k ∈ insert a s, w k * QSq k ω)
                = fun ω => w a * QSq a ω + ∑ k ∈ s, w k * QSq k ω := by
              funext ω
              rw [Finset.sum_insert ha]
            rw [hsu]
            exact ((measurable_const : Measurable fun _ : Ωrand => w a).mul
              (hQSq_meas a)).add ih
      have hm : Measurable Rf := by
        rw [hRf]
        exact key (Finset.range (K + 1))
      exact hm.aestronglyMeasurable
    refine Integrable.mono'
      (integrable_const (∑ k ∈ Finset.range (K + 1), w k * (4 * B1 ^ 2))) hmeas ?_
    filter_upwards [hband_all] with ω hb
    have hnn : 0 ≤ Rf ω := by
      rw [hRf]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (hwnonneg k) (hQSq_nonneg k ω))
    have hle : Rf ω ≤ ∑ k ∈ Finset.range (K + 1), w k * (4 * B1 ^ 2) := by
      rw [hRf]
      exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hb k hk) (hwnonneg k))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hCsum] using hle
  have hZnonneg : ∀ ω : Ωrand, 0 ≤ Zf ω := by
    intro ω
    rw [hZf]
    show 0 ≤ sSup ((fun f : Ωs → ℝ => Gf f ω) '' (Fs : Set (Ωs → ℝ)))
    exact hsup_nonneg Fs (fun f ω => Gf f ω) (fun f _ _ => by rw [hGf]; exact abs_nonneg _) ω
  have hZR : (∫ ω, Zf ω ∂P) ≤ ∫ ω, Rf ω ∂P :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hZnonneg) hIntR
      (Filter.Eventually.of_forall hpoint)
  have hRsum : (∫ ω, Rf ω ∂P) = ∑ k ∈ Finset.range (K + 1), w k * ∫ ω, QSq k ω ∂P := by
    rw [hRf]
    have h1 : (∫ ω, ∑ k ∈ Finset.range (K + 1), w k * QSq k ω ∂P)
        = ∑ k ∈ Finset.range (K + 1), ∫ ω, w k * QSq k ω ∂P :=
      MeasureTheory.integral_finset_sum _
        (fun k _ => (hQSq_int k).const_mul (w k))
    rw [h1]
    exact Finset.sum_congr rfl
      (fun k _ => MeasureTheory.integral_const_mul (w k) (fun ω => QSq k ω))
  have hD2 : ∀ k : ℕ, (∫ ω, QSq k ω ∂P) ≤ 8 * B1 * ∫ ω, Sq k ω ∂P := by
    intro k
    have h := statopia_math_node_2130039367_ac22ae17 Ωs Ωrand P n m hn hm B1 hB1 f0 X sigma
      (T k) hf0_meas (fun f hf => hF_meas f (hFs ((hTmem k f).mp hf).1)) hf0_bound
      (fun f hf => hF_bound f (hFs ((hTmem k f).mp hf).1)) hX_meas hsigma_meas hsigma_law
      hsigma_indep hsigma_indep_X
    have e1 : (∫ ω, QSq k ω ∂P) = ∫ ω, sSup ((fun f : Ωs → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2|) '' ((T k) : Set (Ωs → ℝ))) ∂P := by
      congr 1
      funext ω
      exact hQval k ω
    have e2 : (∫ ω, sSup ((fun f : Ωs → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω))|) '' ((T k) : Set (Ωs → ℝ))) ∂P)
        = ∫ ω, Sq k ω ∂P := by
      congr 1
      funext ω
      exact (hSval k ω).symm
    rw [e1, ← e2]
    exact h
  have hSq_fix : ∀ k : ℕ, (∫ ω, Sq k ω ∂P) ≤ phi ((4 : ℝ) ^ k * r) := by
    intro k
    have hrk : rstar ≤ (4 : ℝ) ^ k * r := by
      have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ k := hone k
      nlinarith [hr, hrpos, h1]
    have hbdd : BddAbove {v : ℝ | ∃ Fs' : Finset (Ωs → ℝ),
        (Fs' : Set (Ωs → ℝ)) ⊆ localizedClass F PX f0 ((4 : ℝ) ^ k * r) ∧
        v = ∫ ω, rademacherFiniteSup X f0 sigma ω Fs' ∂P} := by
      refine ⟨2 * B1, ?_⟩
      rintro v ⟨Fs', hsub', rfl⟩
      have hG : (Fs' : Set (Ωs → ℝ)) ⊆ F := fun f hf => (hsub' hf).1
      have h0 : 0 ≤ᶠ[ae P] (fun ω => rademacherFiniteSup X f0 sigma ω Fs') :=
        Filter.Eventually.of_forall (fun ω => hsup_nonneg Fs'
          (fun f ω => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            sigma i j ω * (f (X i j ω) - f0 (X i j ω))|)
          (fun f _ _ => abs_nonneg _) ω)
      have h := MeasureTheory.integral_mono_of_nonneg h0 (integrable_const (2 * B1))
        (hrad_bound Fs' hG)
      simpa using h
    have hmem : (∫ ω, Sq k ω ∂P) ∈ {v : ℝ | ∃ Fs' : Finset (Ωs → ℝ),
        (Fs' : Set (Ωs → ℝ)) ⊆ localizedClass F PX f0 ((4 : ℝ) ^ k * r) ∧
        v = ∫ ω, rademacherFiniteSup X f0 sigma ω Fs' ∂P} := by
      refine ⟨T k, ?_, ?_⟩
      · intro f hf
        exact ⟨hFs ((hTmem k f).mp hf).1, ((hTmem k f).mp hf).2⟩
      · simp only [hS]
    exact le_trans (le_csSup hbdd hmem) (hfix.2.2.2 _ hrk)
  have hφb : ∀ k : ℕ, phi ((4 : ℝ) ^ k * r) ≤ (2 : ℝ) ^ k * phi r := by
    intro k
    have hrk : r ≤ (4 : ℝ) ^ k * r := by
      have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ k := hone k
      nlinarith [hrpos, h1]
    have hanti : phi ((4 : ℝ) ^ k * r) / Real.sqrt ((4 : ℝ) ^ k * r) ≤
        phi r / Real.sqrt r := hsub.2 hr (hr.trans hrk) hrk
    have hs : 0 < Real.sqrt ((4 : ℝ) ^ k * r) :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le hrpos hrk)
    have hmul : phi ((4 : ℝ) ^ k * r) ≤ phi r / Real.sqrt r * Real.sqrt ((4 : ℝ) ^ k * r) := by
      have h := mul_le_mul_of_nonneg_right hanti hs.le
      rwa [div_mul_cancel₀ _ hs.ne'] at h
    have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    have hsq : Real.sqrt ((4 : ℝ) ^ k * r) = (2 : ℝ) ^ k * Real.sqrt r := by
      rw [Real.sqrt_mul (by positivity), h4, Real.sqrt_sq (by positivity)]
    rw [hsq] at hmul
    refine le_trans hmul ?_
    have hs0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hrpos).ne'
    apply le_of_eq
    calc phi r / Real.sqrt r * ((2 : ℝ) ^ k * Real.sqrt r)
        = (phi r / Real.sqrt r * Real.sqrt r) * (2 : ℝ) ^ k := by ring
      _ = phi r * (2 : ℝ) ^ k := by rw [div_mul_cancel₀ _ hs0]
      _ = (2 : ℝ) ^ k * phi r := by ring
  have hgeomK : ∀ N : ℕ, (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j)
      = 2 - 2 * (1 / 2 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ q ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  have hperterm : ∀ j : ℕ,
      w (j + 1) * phi ((4 : ℝ) ^ (j + 1) * r) ≤ (phi r / r) * (2 * (1 / 2 : ℝ) ^ j) := by
    intro j
    rw [hwsucc j]
    have h2 := hφb (j + 1)
    have h4j : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    have hstep1 : (((4 : ℝ) ^ j + 1) * r)⁻¹ ≤ (((4 : ℝ) ^ j) * r)⁻¹ := by
      have hp : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
      gcongr
      nlinarith
    have hstep2 : (((4 : ℝ) ^ j) * r)⁻¹ * ((2 : ℝ) ^ (j + 1) * phi r)
        = (phi r / r) * (2 * (1 / 2 : ℝ) ^ j) := by
      have hinv : (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := by
        rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, inv_pow]
      rw [h4j, hinv, pow_succ]
      field_simp
      ring
    calc (((4 : ℝ) ^ j + 1) * r)⁻¹ * phi ((4 : ℝ) ^ (j + 1) * r)
        ≤ (((4 : ℝ) ^ j + 1) * r)⁻¹ * ((2 : ℝ) ^ (j + 1) * phi r) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (((4 : ℝ) ^ j) * r)⁻¹ * ((2 : ℝ) ^ (j + 1) * phi r) :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ = (phi r / r) * (2 * (1 / 2 : ℝ) ^ j) := hstep2
  have hgeom : ∑ k ∈ Finset.range (K + 1), w k * phi ((4 : ℝ) ^ k * r) ≤ 5 * (phi r / r) := by
    have hsplit : ∑ k ∈ Finset.range (K + 1), w k * phi ((4 : ℝ) ^ k * r)
        = w 0 * phi r + ∑ j ∈ Finset.range K, w (j + 1) * phi ((4 : ℝ) ^ (j + 1) * r) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul]
      ring
    have hw0' : w 0 * phi r = phi r / r := by
      rw [hw0]
      ring
    have hrest : ∑ j ∈ Finset.range K, w (j + 1) * phi ((4 : ℝ) ^ (j + 1) * r)
        ≤ ∑ j ∈ Finset.range K, (phi r / r) * (2 * (1 / 2 : ℝ) ^ j) :=
      Finset.sum_le_sum (fun j _ => hperterm j)
    have hsum2 : ∑ j ∈ Finset.range K, (phi r / r) * (2 * (1 / 2 : ℝ) ^ j)
        = (phi r / r) * (2 * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    have hgeo : ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j ≤ 2 := by
      rw [hgeomK K]
      have hp : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ K := by positivity
      linarith
    have hc : (0 : ℝ) ≤ phi r / r := div_nonneg hφr hrpos.le
    rw [hsplit, hw0']
    calc phi r / r + ∑ j ∈ Finset.range K, w (j + 1) * phi ((4 : ℝ) ^ (j + 1) * r)
        ≤ phi r / r + ∑ j ∈ Finset.range K, (phi r / r) * (2 * (1 / 2 : ℝ) ^ j) := by
          linarith
      _ = phi r / r + (phi r / r) * (2 * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) := by
          rw [hsum2]
      _ ≤ phi r / r + (phi r / r) * (2 * 2) := by
          have h2 : (0 : ℝ) ≤ (phi r / r) * 2 := by positivity
          nlinarith [hgeo]
      _ = 5 * (phi r / r) := by ring
  have hfinal : ∑ k ∈ Finset.range (K + 1), w k * ∫ ω, QSq k ω ∂P ≤ 40 * B1 * phi r / r := by
    have hstep1 : ∑ k ∈ Finset.range (K + 1), w k * ∫ ω, QSq k ω ∂P
        ≤ ∑ k ∈ Finset.range (K + 1), w k * (8 * B1 * phi ((4 : ℝ) ^ k * r)) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hwnonneg k)
      exact le_trans (hD2 k) (mul_le_mul_of_nonneg_left (hSq_fix k) (by positivity))
    have hstep2 : ∑ k ∈ Finset.range (K + 1), w k * (8 * B1 * phi ((4 : ℝ) ^ k * r))
        = 8 * B1 * ∑ k ∈ Finset.range (K + 1), w k * phi ((4 : ℝ) ^ k * r) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    calc ∑ k ∈ Finset.range (K + 1), w k * ∫ ω, QSq k ω ∂P
        ≤ ∑ k ∈ Finset.range (K + 1), w k * (8 * B1 * phi ((4 : ℝ) ^ k * r)) := hstep1
      _ = 8 * B1 * ∑ k ∈ Finset.range (K + 1), w k * phi ((4 : ℝ) ^ k * r) := hstep2
      _ ≤ 8 * B1 * (5 * (phi r / r)) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 40 * B1 * phi r / r := by ring
  have hbridge : (∫ ω, sSup ((fun f : Ωs → ℝ =>
      |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 / (predError PX f0 f + r)|)
        '' (Fs : Set (Ωs → ℝ))) ∂P) = ∫ ω, Zf ω ∂P := by
    congr 1
    funext ω
    rw [hZf, hGf]
  rw [hbridge]
  exact le_trans hZR (le_trans (le_of_eq hRsum) hfinal)
  /- @proof-region region.target-node.session.7702e9e901e81608 end -/

end

end Statlib.Imported

