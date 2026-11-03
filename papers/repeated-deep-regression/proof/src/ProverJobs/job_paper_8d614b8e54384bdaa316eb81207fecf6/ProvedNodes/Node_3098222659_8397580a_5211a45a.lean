import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_1390765457_210d1e15_5d8f5653
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_2130039367_ac22ae17_25b6ec44
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_2210185272_b87383a3_4849efda
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_2912637286_53196a25_075e65c7

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
theorem statopia_math_node_3098222659_8397580a : ∀ (B1 : ℝ) (hB1 : 0 < B1)
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
    (hX_law : ∀ p : Fin n × Fin m, Measure.map (X p.1 p.2) P = PX)
    (hX_indep : iIndepFun (fun p : Fin n × Fin m => X p.1 p.2) P)
    (sigma : Fin n → Fin m → Ωrand → ℝ)
    (hsigma_meas : ∀ p : Fin n × Fin m, Measurable (sigma p.1 p.2))
    (hsigma_law : ∀ p : Fin n × Fin m, Measure.map (sigma p.1 p.2) P = rademacherLaw)
    (hsigma_indep : iIndepFun (fun p : Fin n × Fin m => sigma p.1 p.2) P)
    (hsigma_indep_X : IndepFun (fun ω => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
      (fun ω => fun p : Fin n × Fin m => X p.1 p.2 ω) P)
    (phi : ℝ → ℝ) (rstar : ℝ)
    (hfix : IsRademacherFixedPoint F PX f0 X sigma P phi rstar)
    (r : ℝ) (hr : rstar ≤ r),
    sSup {v : ℝ | ∃ Fs : Finset (Ωs → ℝ), (Fs : Set (Ωs → ℝ)) ⊆ F ∧
      v = ∫ ω, sSup ((fun f : Ωs → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          ((∫ x, (f x - f0 x) ^ 2 ∂PX) - (f (X i j ω) - f0 (X i j ω)) ^ 2) /
            ((∫ x, (f x - f0 x) ^ 2 ∂PX) + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P}
      ≤ 80 * B1 * phi r / r := by
  /- @proof-region region.target-node.session.5a780266b66b1812 begin -/
  intro B1 hB1 Ωs hΩs PX hPX f0 F hf0_meas hF_meas hf0_bound hF_bound hF_int
    Ωrand hΩrand P hP n m hn hm X hX_meas hX_law hX_indep sigma hsigma_meas hsigma_law
    hsigma_indep hsigma_indep_X phi rstar hfix r hr
  have hrstar_pos : 0 < rstar := hfix.1
  have hr0 : 0 < r := lt_of_lt_of_le hrstar_pos hr
  have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hsub : IsSubRootOn phi (Set.Ici rstar) := hfix.2.1
  have hphi_nonneg : 0 ≤ phi r := by
    have h1 : 0 ≤ phi r / Real.sqrt r := hsub.1 r (Set.mem_Ici.mpr hr)
    have h2 : 0 ≤ Real.sqrt r := le_of_lt hsqrt_pos
    have h3 : 0 ≤ (phi r / Real.sqrt r) * Real.sqrt r := mul_nonneg h1 h2
    rwa [div_mul_cancel₀ _ (ne_of_gt hsqrt_pos)] at h3
  classical
  have sup_empty : sSup (∅ : Set ℝ) = 0 := by simp
  have sup_singleton : ∀ x : ℝ, sSup ({x} : Set ℝ) = x := by
    intro x
    refine le_antisymm (csSup_le ⟨x, rfl⟩ (by rintro y rfl; exact le_rfl))
      (le_csSup ⟨x, by rintro y rfl; exact le_rfl⟩ rfl)
  have meas_sup : ∀ (Fs : Finset (Ωs → ℝ)) (G : (Ωs → ℝ) → Ωrand → ℝ) (C : ℝ),
      (∀ f ∈ Fs, Measurable (G f)) → (∀ f ∈ Fs, ∀ ω, |G f ω| ≤ C) →
      (∀ f ∈ Fs, ∀ ω, 0 ≤ G f ω) →
      Measurable (fun ω => sSup ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ)))) := by
    intro Fs
    induction Fs using Finset.induction with
    | empty =>
      intro G C _ _ _
      have h : (fun ω : Ωrand =>
          sSup ((fun f => G f ω) '' ((∅ : Finset (Ωs → ℝ)) : Set (Ωs → ℝ)))) = fun _ => 0 := by
        funext ω
        rw [Finset.coe_empty, Set.image_empty, sup_empty]
      rw [h]
      exact measurable_const
    | insert a s ha ih =>
      intro G C hG hb hpos
      have hGa : Measurable (G a) := hG a (Finset.mem_insert_self a s)
      have hs : Measurable (fun ω => sSup ((fun f => G f ω) '' (s : Set (Ωs → ℝ)))) :=
        ih G C (fun f hf => hG f (Finset.mem_insert_of_mem hf))
          (fun f hf ω => hb f (Finset.mem_insert_of_mem hf) ω)
          (fun f hf ω => hpos f (Finset.mem_insert_of_mem hf) ω)
      have hbdd : ∀ ω, BddAbove ((fun f => G f ω) '' (s : Set (Ωs → ℝ))) := fun ω =>
        ⟨C, by
          rintro y ⟨f, hf, rfl⟩
          exact (abs_le.mp (hb f (Finset.mem_insert_of_mem hf) ω)).2⟩
      have heq : (fun ω : Ωrand => sSup
            ((fun f => G f ω) '' ((insert a s : Finset (Ωs → ℝ)) : Set (Ωs → ℝ))))
          = fun ω => max (G a ω) (sSup ((fun f => G f ω) '' (s : Set (Ωs → ℝ)))) := by
        funext ω
        rw [Finset.coe_insert, Set.image_insert_eq]
        by_cases hne : s.Nonempty
        · obtain ⟨f₀, hf₀⟩ := hne
          exact csSup_insert (hbdd ω) ⟨G f₀ ω, f₀, hf₀, rfl⟩
        · have himg : ((fun f => G f ω) '' (s : Set (Ωs → ℝ))) = ∅ := by
            ext y
            constructor
            · rintro ⟨f, hf, -⟩
              exact absurd ⟨f, hf⟩ hne
            · intro hy
              exact absurd hy (by simp)
          rw [himg, sup_empty]
          have hins : (insert (G a ω) (∅ : Set ℝ)) = ({G a ω} : Set ℝ) := by simp
          rw [hins, sup_singleton]
          exact le_antisymm (le_max_left _ _)
            (max_le le_rfl (hpos a (Finset.mem_insert_self a s) ω))
      rw [heq]
      exact hGa.sup hs
  have integrable_sup : ∀ (Fs : Finset (Ωs → ℝ)) (G : (Ωs → ℝ) → Ωrand → ℝ) (C : ℝ),
      0 ≤ C → (∀ f ∈ Fs, Measurable (G f)) → (∀ f ∈ Fs, ∀ ω, |G f ω| ≤ C) →
      (∀ f ∈ Fs, ∀ ω, 0 ≤ G f ω) →
      Integrable (fun ω => sSup ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ)))) P := by
    intro Fs G C hC hG hb hpos
    have hm : Measurable (fun ω => sSup ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ)))) :=
      meas_sup Fs G C hG hb hpos
    refine Integrable.mono' (integrable_const C) hm.aestronglyMeasurable ?_
    filter_upwards with ω
    have hbdd : BddAbove ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ))) :=
      ⟨C, by
        rintro y ⟨f, hf, rfl⟩
        exact (abs_le.mp (hb f hf ω)).2⟩
    have hupper : sSup ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ))) ≤ C := by
      by_cases hne : Fs.Nonempty
      · refine csSup_le ⟨_, ⟨hne.choose, hne.choose_spec, rfl⟩⟩ ?_
        rintro y ⟨f, hf, rfl⟩
        exact (abs_le.mp (hb f hf ω)).2
      · have himg : ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ))) = ∅ := by
          ext y
          constructor
          · rintro ⟨f, hf, -⟩
            exact absurd ⟨f, hf⟩ hne
          · intro hy
            exact absurd hy (by simp)
        rw [himg, sup_empty]
        exact hC
    have hlower : 0 ≤ sSup ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ))) := by
      by_cases hne : Fs.Nonempty
      · obtain ⟨f₀, hf₀⟩ := hne
        exact le_trans (hpos f₀ hf₀ ω) (le_csSup hbdd ⟨f₀, hf₀, rfl⟩)
      · have himg : ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ))) = ∅ := by
          ext y
          constructor
          · rintro ⟨f, hf, -⟩
            exact absurd ⟨f, hf⟩ hne
          · intro hy
            exact absurd hy (by simp)
        rw [himg, sup_empty]
    have h1 : ‖sSup ((fun f => G f ω) '' (Fs : Set (Ωs → ℝ)))‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg hlower]
      exact hupper
    simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using h1
  have hkey : ∀ Fs : Finset (Ωs → ℝ), (Fs : Set (Ωs → ℝ)) ⊆ F →
      (∫ ω, sSup ((fun f : Ωs → ℝ =>
          |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) /
              (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P)
        ≤ 80 * B1 * phi r / r := by
    intro Fs hFs
    have hmemF : ∀ f ∈ Fs, f ∈ F := fun f hf => hFs (by simpa using hf)
    have hB1nonneg : (0 : ℝ) ≤ B1 := le_of_lt hB1
    have hpt : ∀ f ∈ Fs, ∀ x : Ωs, 0 ≤ (f x - f0 x) ^ 2 ∧ (f x - f0 x) ^ 2 ≤ 4 * B1 ^ 2 := by
      intro f hf x
      have h1 : |f x| ≤ B1 := hF_bound f (hmemF f hf) x
      have h2 : |f0 x| ≤ B1 := hf0_bound x
      refine ⟨sq_nonneg _, ?_⟩
      have h3 : |f x - f0 x| ≤ 2 * B1 := by
        rw [abs_le]
        have ha := abs_le.mp h1
        have hb := abs_le.mp h2
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
      have h4 : |f x - f0 x| ^ 2 ≤ (2 * B1) ^ 2 := by
        nlinarith [h3, abs_nonneg (f x - f0 x), sq_nonneg (2 * B1 - |f x - f0 x|)]
      calc (f x - f0 x) ^ 2 = |f x - f0 x| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * B1) ^ 2 := h4
        _ = 4 * B1 ^ 2 := by ring
    have hlow : ∀ f ∈ Fs, 0 ≤ predError PX f0 f := by
      intro f hf
      exact MeasureTheory.integral_nonneg (fun x => (hpt f hf x).1)
    have hup : ∀ f ∈ Fs, predError PX f0 f ≤ 4 * B1 ^ 2 := by
      intro f hf
      have h1 : ∫ x, (f x - f0 x) ^ 2 ∂PX ≤ ∫ x, (4 * B1 ^ 2 : ℝ) ∂PX :=
        MeasureTheory.integral_mono (hf := hF_int f (hmemF f hf))
          (hg := integrable_const (4 * B1 ^ 2))
          (h := fun x => (hpt f hf x).2)
      have h2 : (∫ x, (4 * B1 ^ 2 : ℝ) ∂PX) = 4 * B1 ^ 2 := by simp
      calc predError PX f0 f = ∫ x, (f x - f0 x) ^ 2 ∂PX := rfl
        _ ≤ ∫ x, (4 * B1 ^ 2 : ℝ) ∂PX := h1
        _ = 4 * B1 ^ 2 := h2
    have helem : ∀ f ∈ Fs, 0 ≤ predError PX f0 f ∧ predError PX f0 f ≤ 4 * B1 ^ 2 :=
      fun f hf => ⟨hlow f hf, hup f hf⟩
    have hpos : ∀ f ∈ Fs, 0 < predError PX f0 f + r := fun f hf => by
      have := (helem f hf).1
      linarith
    have hsym := statopia_math_node_2912637286_53196a25 B1 hB1 PX hPX f0 F hf0_meas hF_meas
      hf0_bound hF_bound hF_int P hP n m hn hm X (fun i j => hX_meas (i, j))
      (fun i j => hX_law (i, j)) hX_indep sigma (fun i j => hsigma_meas (i, j))
      (fun i j => hsigma_law (i, j)) hsigma_indep hsigma_indep_X r hr0 Fs hFs
    have hpeel : (∫ ω, sSup ((fun f : Ωs → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 /
            (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P)
        ≤ 40 * B1 * phi r / r := by
      exact statopia_math_node_2210185272_b87383a3 B1 hB1 PX f0 F hf0_meas hF_meas
        hf0_bound hF_bound hF_int P n m hn hm X hX_meas sigma hsigma_meas hsigma_law
        hsigma_indep hsigma_indep_X phi rstar hfix r hr Fs hFs
    have h2le : 2 * (∫ ω, sSup ((fun f : Ωs → ℝ =>
        |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 /
            (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P)
        ≤ 2 * (40 * B1 * phi r / r) := by
      linarith [hpeel]
    have h3 : 2 * (40 * B1 * phi r / r) = 80 * B1 * phi r / r := by ring
    exact le_trans hsym (le_trans h2le (le_of_eq h3))
  have hball : ∀ v ∈ {v : ℝ | ∃ Fs : Finset (Ωs → ℝ), (Fs : Set (Ωs → ℝ)) ⊆ F ∧
        v = ∫ ω, sSup ((fun f : Ωs → ℝ =>
          |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) /
              (predError PX f0 f + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P},
      v ≤ 80 * B1 * phi r / r := by
    rintro v ⟨Fs, hFs, rfl⟩
    exact hkey Fs hFs
  refine csSup_le ⟨_, ⟨∅, by simp, rfl⟩⟩ hball
  /- @proof-region region.target-node.session.5a780266b66b1812 end -/

end

end Statlib.Imported

