import Statlib.StatFoundation.EmpiricalProcess.Symmetrization
import Statlib.StatFoundation.Vocabulary.EmpiricalProcess
import Lean
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Vocabulary
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.Base
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_1390765457_210d1e15_5d8f5653
import ProverJobs.job_paper_8d614b8e54384bdaa316eb81207fecf6.ProvedNodes.Node_1903948443_c79ced3a_9da0958a

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
theorem statopia_math_node_2912637286_53196a25 : ∀ (B1 : ℝ) (hB1 : 0 < B1)
    {Ωs : Type*} [MeasurableSpace Ωs]
    (PX : Measure Ωs) (hPX : IsProbabilityMeasure PX)
    (f0 : Ωs → ℝ) (F : Set (Ωs → ℝ))
    (hf0_meas : Measurable f0) (hF_meas : ∀ f ∈ F, Measurable f)
    (hf0_bound : ∀ x : Ωs, |f0 x| ≤ B1)
    (hF_bound : ∀ f ∈ F, ∀ x : Ωs, |f x| ≤ B1)
    (hF_int : ∀ f ∈ F, Integrable (fun x : Ωs => (f x - f0 x) ^ 2) PX)
    {Ωrand : Type*} [MeasurableSpace Ωrand] (P : Measure Ωrand)
    (hP : IsProbabilityMeasure P)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (X : Fin n → Fin m → Ωrand → Ωs)
    (hX_meas : ∀ (i : Fin n) (j : Fin m), Measurable (X i j))
    (hX_law : ∀ (i : Fin n) (j : Fin m), Measure.map (X i j) P = PX)
    (hX_indep : iIndepFun (fun p : Fin n × Fin m => X p.1 p.2) P)
    (sigma : Fin n → Fin m → Ωrand → ℝ)
    (hsigma_meas : ∀ (i : Fin n) (j : Fin m), Measurable (sigma i j))
    (hsigma_law : ∀ (i : Fin n) (j : Fin m), Measure.map (sigma i j) P = rademacherLaw)
    (hsigma_indep : iIndepFun (fun p : Fin n × Fin m => sigma p.1 p.2) P)
    (hsigma_indep_X : IndepFun (fun ω => fun p : Fin n × Fin m => sigma p.1 p.2 ω)
      (fun ω => fun p : Fin n × Fin m => X p.1 p.2 ω) P)
    (r : ℝ) (hr : 0 < r) (Fs : Finset (Ωs → ℝ)) (hFs : (Fs : Set (Ωs → ℝ)) ⊆ F),
    ∫ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        ((∫ x, (f x - f0 x) ^ 2 ∂PX) - (f (X i j ω) - f0 (X i j ω)) ^ 2) /
          ((∫ x, (f x - f0 x) ^ 2 ∂PX) + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P
      ≤ 2 * ∫ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 /
          ((∫ x, (f x - f0 x) ^ 2 ∂PX) + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P := by
  /- @proof-region region.target-node.session.cb0a2cba48aff83e begin -/
  intro B1 hB1 Ωs instΩs PX hPX f0 F hf0m hFm hf0b hFb hFi Ωrand instΩrand P hP n m hn hm X
    hXm hXl hXi sigma hsm hsl hsi hsX r hr Fs hFs
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  set e : Fin n × Fin m ≃ Fin (n * m) := Fintype.equivFinOfCardEq (by simp) with he
  set Xf : Fin (n * m) → Ωrand → Ωs := fun k => X (e.symm k).1 (e.symm k).2 with hXf
  set eF : ↥Fs ≃ Fin Fs.card := Fintype.equivFinOfCardEq (by simp) with heF
  set G : Fin Fs.card → Ωs → ℝ := fun j x =>
    (((eF.symm j : ↥Fs) : Ωs → ℝ) x - f0 x) ^ 2 /
      (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) with hG
  have hXfm : ∀ k, Measurable (Xf k) := by
    intro k
    simpa only [hXf] using hXm (e.symm k).1 (e.symm k).2
  have hXfi : iIndepFun Xf P := by
    have hinj : Function.Injective (fun k : Fin (n * m) => e.symm k) :=
      fun a b hab => e.symm.injective hab
    simpa only [hXf] using hXi.precomp (g := fun k : Fin (n * m) => e.symm k) hinj
  have hXfid : ∀ i j, IdentDistrib (Xf i) (Xf j) P P := by
    intro i j
    have hi : Measure.map (Xf i) P = PX := by
      simpa only [hXf] using hXl (e.symm i).1 (e.symm i).2
    have hj : Measure.map (Xf j) P = PX := by
      simpa only [hXf] using hXl (e.symm j).1 (e.symm j).2
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hXf] using (hXm (e.symm i).1 (e.symm i).2).aemeasurable
    · simpa only [hXf] using (hXm (e.symm j).1 (e.symm j).2).aemeasurable
    · exact hi.trans hj.symm
  have hGm : ∀ j, Measurable (G j) := by
    intro j
    have hf : Measurable ((eF.symm j : ↥Fs) : Ωs → ℝ) := hFm _ (hFs (eF.symm j).2)
    simp only [hG]
    measurability
  have hint : ∀ (i : Fin (n * m)) (j : Fin Fs.card), Integrable (G j ∘ Xf i) P := by
    intro i j
    have hFF : ((eF.symm j : ↥Fs) : Ωs → ℝ) ∈ F := hFs (eF.symm j).2
    have ha0 : 0 ≤ predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) :=
      integral_nonneg (fun x => sq_nonneg _)
    have hden : 0 < predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r := by linarith
    have hb : ∀ ω : Ωrand, |(G j ∘ Xf i) ω| ≤ 4 * B1 ^ 2 / r := by
      intro ω
      have hpt : |((eF.symm j : ↥Fs) : Ωs → ℝ) (Xf i ω) - f0 (Xf i ω)| ≤ 2 * B1 := by
        have h1 := abs_le.mp (hFb _ hFF (Xf i ω))
        have h2 := abs_le.mp (hf0b (Xf i ω))
        rw [abs_le]
        constructor <;> linarith
      obtain ⟨hp1, hp2⟩ := abs_le.mp hpt
      have hsq : (((eF.symm j : ↥Fs) : Ωs → ℝ) (Xf i ω) - f0 (Xf i ω)) ^ 2 ≤ 4 * B1 ^ 2 := by
        nlinarith
      have hval : (G j ∘ Xf i) ω
          = (((eF.symm j : ↥Fs) : Ωs → ℝ) (Xf i ω) - f0 (Xf i ω)) ^ 2
            / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) := by
        simp only [Function.comp_apply, hG]
      rw [hval, abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hden))]
      have hkey : (((eF.symm j : ↥Fs) : Ωs → ℝ) (Xf i ω) - f0 (Xf i ω)) ^ 2
            / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) ≤ 4 * B1 ^ 2 / r := by
        have hd : (0:ℝ) < (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) * r :=
          mul_pos hden hr
        have hnum : 0 ≤ 4 * B1 ^ 2 * (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)
            - (((eF.symm j : ↥Fs) : Ωs → ℝ) (Xf i ω) - f0 (Xf i ω)) ^ 2 * r := by
          nlinarith [hsq, ha0, hr, sq_nonneg B1]
        have heq : 4 * B1 ^ 2 / r
            - (((eF.symm j : ↥Fs) : Ωs → ℝ) (Xf i ω) - f0 (Xf i ω)) ^ 2
              / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)
            = (4 * B1 ^ 2 * (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)
                - (((eF.symm j : ↥Fs) : Ωs → ℝ) (Xf i ω) - f0 (Xf i ω)) ^ 2 * r)
              / ((predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) * r) := by
          field_simp
        rw [← sub_nonneg, heq]
        exact div_nonneg hnum (le_of_lt hd)
      exact hkey
    refine Integrable.mono' (g := fun _ : Ωrand => 4 * B1 ^ 2 / r) (integrable_const _) ?_ ?_
    · exact ((hGm j).comp (hXfm i)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs]
      exact hb ω
  by_cases hFs0 : Fs = ∅
  · simp only [hFs0, Finset.coe_empty, Set.image_empty]
    simp
  · have hFscard : 0 < Fs.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hFs0)
    have hA0 : ∀ j : Fin Fs.card, 0 ≤ predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) :=
      fun j => integral_nonneg (fun x => sq_nonneg _)
    have hAden : ∀ j : Fin Fs.card,
        0 < predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r :=
      fun j => by linarith [hA0 j]
    have hNpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) := by
      have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    have hN0 : ((n : ℝ) * (m : ℝ)) ≠ 0 := ne_of_gt hNpos
    have halg : ∀ (A r S T c N : ℝ), c * N = 1 → T = N * (A / (A + r)) - S →
        c * S - A / (A + r) = -(c * T) := by
      intro A r S T c N hc hT
      rw [hT, mul_sub, ← mul_assoc, hc, one_mul]
      ring
    have hbridge : ∀ (Ψ : (Ωs → ℝ) → ℝ), (∀ f ∈ Fs, 0 ≤ Ψ f) →
        sSup (Ψ '' (Fs : Set (Ωs → ℝ)))
          = ⨆ j : Fin Fs.card, Ψ ((eF.symm j : ↥Fs) : Ωs → ℝ) := by
      intro Ψ hΨ0
      haveI : Nonempty (Fin Fs.card) := ⟨⟨0, hFscard⟩⟩
      have hfin : (Ψ '' (Fs : Set (Ωs → ℝ))).Finite := (Finset.finite_toSet Fs).image Ψ
      have hbdd' : BddAbove (Ψ '' (Fs : Set (Ωs → ℝ))) := hfin.bddAbove
      have hrange : (Set.range fun j : Fin Fs.card => Ψ ((eF.symm j : ↥Fs) : Ωs → ℝ))
          = Ψ '' (Fs : Set (Ωs → ℝ)) := by
        ext y
        constructor
        · rintro ⟨jj, rfl⟩
          exact ⟨_, (eF.symm jj).2, rfl⟩
        · rintro ⟨ff, hf, rfl⟩
          exact ⟨eF ⟨ff, hf⟩, by simp⟩
      have hbdd : BddAbove (Set.range fun j : Fin Fs.card => Ψ ((eF.symm j : ↥Fs) : Ωs → ℝ)) := by
        rw [hrange]
        exact hbdd'
      refine le_antisymm ?_ ?_
      · refine Real.sSup_le ?_ ?_
        · rintro x ⟨ff, hf, rfl⟩
          have hfs : ((eF.symm (eF ⟨ff, hf⟩) : ↥Fs) : Ωs → ℝ) = ff := by simp
          rw [← hfs]
          exact le_ciSup hbdd _
        · exact le_trans (hΨ0 _ (eF.symm ⟨0, hFscard⟩).2) (le_ciSup hbdd ⟨0, hFscard⟩)
      · refine ciSup_le ?_
        intro j
        exact le_csSup hbdd' ⟨_, (eF.symm j).2, rfl⟩
    have hGint : ∀ j : Fin Fs.card,
        ∫ ω', G j (Xf ⟨0, hnm⟩ ω') ∂P
          = predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
            / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) := by
      intro j
      have hmap : Measure.map (Xf ⟨0, hnm⟩) P = PX := by
        simpa only [hXf] using hXl (e.symm ⟨0, hnm⟩).1 (e.symm ⟨0, hnm⟩).2
      calc ∫ ω', G j (Xf ⟨0, hnm⟩ ω') ∂P
          = ∫ x, G j x ∂(Measure.map (Xf ⟨0, hnm⟩) P) :=
            (MeasureTheory.integral_map (hXfm _).aemeasurable (hGm j).aestronglyMeasurable).symm
        _ = ∫ x, G j x ∂PX := by rw [hmap]
        _ = predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
              / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) := by
            simp only [hG]
            rw [MeasureTheory.integral_div]
            rfl
    have hGsum : ∀ (j : Fin Fs.card) (ω : Ωrand),
        ∑ k : Fin (n * m), G j (Xf k ω)
          = ∑ i : Fin n, ∑ j' : Fin m,
              (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2
                / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) := by
      intro j ω
      have h1 : ∑ k : Fin (n * m), G j (Xf k ω)
          = ∑ p : Fin n × Fin m, G j (X p.1 p.2 ω) := by
        simp only [hXf]
        rw [Equiv.sum_comp e.symm (fun p : Fin n × Fin m => G j (X p.1 p.2 ω))]
      rw [h1, Fintype.sum_prod_type]
    have hbddGen : ∀ (g : Fin Fs.card → ℝ), BddAbove (Set.range g) := by
      intro g
      refine ⟨∑ j : Fin Fs.card, |g j|, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact le_trans (le_abs_self (g j))
        (Finset.single_le_sum (f := fun j => |g j|) (fun i _ => abs_nonneg (g i))
          (Finset.mem_univ j))
    have key1 : (fun ω : Ωrand => sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|) ''
          (Fs : Set (Ωs → ℝ))))
        = fun ω : Ωrand => Statlib.StatFoundation.Vocabulary.uniformDeviation (n * m) G P (Xf ⟨0, hnm⟩) (fun k => Xf k ω) := by
      funext ω
      haveI : Nonempty (Fin Fs.card) := ⟨⟨0, hFscard⟩⟩
      rw [hbridge (fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          (predError PX f0 f - (f (X i j ω) - f0 (X i j ω)) ^ 2) / (predError PX f0 f + r)|)
        (fun f hf => abs_nonneg _)]
      rw [show Statlib.StatFoundation.Vocabulary.uniformDeviation (n * m) G P (Xf ⟨0, hnm⟩)
            (fun k => Xf k ω)
          = ⨆ j : Fin Fs.card, |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), G j (Xf k ω)
              - ∫ ω', G j (Xf ⟨0, hnm⟩ ω') ∂P| from rfl]
      have hEq : ∀ j : Fin Fs.card,
          |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j' : Fin m,
              (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
                - (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2)
                / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)|
            = |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), G j (Xf k ω)
                - ∫ ω', G j (Xf ⟨0, hnm⟩ ω') ∂P| := by
        intro j
        have hR : ((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), G j (Xf k ω)
            - ∫ ω', G j (Xf ⟨0, hnm⟩ ω') ∂P
            = -(((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j' : Fin m,
                (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
                  - (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2)
                / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)) := by
          rw [hGsum j ω, hGint j]
          simp only [Nat.cast_mul]
          refine halg (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)) r
            (∑ i : Fin n, ∑ j' : Fin m,
              (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2
                / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r))
            (∑ i : Fin n, ∑ j' : Fin m,
              (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
                - (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2)
                / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r))
            ((n : ℝ) * (m : ℝ))⁻¹ ((n : ℝ) * (m : ℝ)) ?_ ?_
          · exact inv_mul_cancel₀ hN0
          · have hconst : ∑ i : Fin n, ∑ j' : Fin m,
                predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
                  / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)
                = ((n : ℝ) * (m : ℝ)) * (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
                    / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
            simp only [sub_div, Finset.sum_sub_distrib, hconst]
        rw [hR, abs_neg]
      refine le_antisymm ?_ ?_
      · refine ciSup_le (fun j => ?_)
        rw [hEq j]
        exact le_ciSup (f := fun j => |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m), G j (Xf k ω)
          - ∫ ω', G j (Xf ⟨0, hnm⟩ ω') ∂P|) (hbddGen _) j
      · refine ciSup_le (fun j => ?_)
        rw [← hEq j]
        exact le_ciSup (f := fun j => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j' : Fin m,
          (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ)
            - (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2)
            / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)|) (hbddGen _) j
    have hsign : ∀ b : Bool,
        (if Statlib.StatFoundation.Vocabulary.rademacherSign b = 1 then (1 : ℝ) else -1)
          = Statlib.StatFoundation.Vocabulary.rademacherSign b := by
      intro b
      have hb1 : Statlib.StatFoundation.Vocabulary.rademacherSign true = 1 := by
        simp [Statlib.StatFoundation.Vocabulary.rademacherSign]
      have hb0 : Statlib.StatFoundation.Vocabulary.rademacherSign false = -1 := by
        simp [Statlib.StatFoundation.Vocabulary.rademacherSign]
      cases b
      · rw [hb0, if_neg (by norm_num : (-1:ℝ) ≠ 1)]
      · rw [hb1, if_pos rfl]
    have hGbound : ∀ (j : Fin Fs.card) (y : Ωs), |G j y| ≤ 4 * B1 ^ 2 / r := by
      intro j y
      have hFF : ((eF.symm j : ↥Fs) : Ωs → ℝ) ∈ F := hFs (eF.symm j).2
      have hpt : |((eF.symm j : ↥Fs) : Ωs → ℝ) y - f0 y| ≤ 2 * B1 := by
        have h1 := abs_le.mp (hFb _ hFF y)
        have h2 := abs_le.mp (hf0b y)
        rw [abs_le]
        constructor <;> linarith
      obtain ⟨hp1, hp2⟩ := abs_le.mp hpt
      have hsq : (((eF.symm j : ↥Fs) : Ωs → ℝ) y - f0 y) ^ 2 ≤ 4 * B1 ^ 2 := by nlinarith
      have hden : 0 < predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r := hAden j
      have hval : G j y = (((eF.symm j : ↥Fs) : Ωs → ℝ) y - f0 y) ^ 2
            / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) := by
        simp only [hG]
      rw [hval, abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hden))]
      have hd : (0:ℝ) < (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) * r :=
        mul_pos hden hr
      have hnum : 0 ≤ 4 * B1 ^ 2 * (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)
          - (((eF.symm j : ↥Fs) : Ωs → ℝ) y - f0 y) ^ 2 * r := by
        nlinarith [hsq, hA0 j, hr, sq_nonneg B1]
      have heq : 4 * B1 ^ 2 / r
          - (((eF.symm j : ↥Fs) : Ωs → ℝ) y - f0 y) ^ 2
            / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)
          = (4 * B1 ^ 2 * (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)
              - (((eF.symm j : ↥Fs) : Ωs → ℝ) y - f0 y) ^ 2 * r)
            / ((predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) * r) := by
        field_simp
      rw [← sub_nonneg, heq]
      exact div_nonneg hnum (le_of_lt hd)
    have hΦm : Measurable fun q : (Fin (n * m) → ℝ) × (Fin (n * m) → Ωs) =>
        ⨆ j : Fin Fs.card,
          |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
            (if q.1 k = 1 then (1 : ℝ) else -1) * G j (q.2 k)| := by
      apply Measurable.iSup
      intro j
      refine Measurable.abs ?_
      refine measurable_const.mul ?_
      refine Finset.measurable_sum _ (fun k _ => ?_)
      · refine Measurable.mul ?_ ?_
        · have hi1 : Measurable fun q : (Fin (n * m) → ℝ) × (Fin (n * m) → Ωs) => q.1 k :=
            (measurable_pi_apply k).comp measurable_fst
          have hi2 : Measurable fun t : ℝ => (if t = 1 then (1 : ℝ) else -1) :=
            Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const
          exact hi2.comp hi1
        · have hj1 : Measurable fun q : (Fin (n * m) → ℝ) × (Fin (n * m) → Ωs) => q.2 k :=
            (measurable_pi_apply k).comp measurable_snd
          exact (hGm j).comp hj1
    have hΦC : ∀ (s : Fin (n * m) → ℝ) (x : Fin (n * m) → Ωs),
        |(⨆ j : Fin Fs.card,
          |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
            (if s k = 1 then (1 : ℝ) else -1) * G j (x k)|)| ≤ 4 * B1 ^ 2 / r := by
      intro s x
      haveI : Nonempty (Fin Fs.card) := ⟨⟨0, hFscard⟩⟩
      have hNinv : (0:ℝ) < ((n * m : ℕ) : ℝ)⁻¹ := by
        have hpos : (0:ℝ) < ((n * m : ℕ) : ℝ) := by exact_mod_cast hnm
        exact inv_pos.mpr hpos
      have hterm : ∀ j : Fin Fs.card,
          |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
            (if s k = 1 then (1 : ℝ) else -1) * G j (x k)| ≤ 4 * B1 ^ 2 / r := by
        intro j
        have hstep : |∑ k : Fin (n * m),
            (if s k = 1 then (1 : ℝ) else -1) * G j (x k)|
            ≤ ((n * m : ℕ) : ℝ) * (4 * B1 ^ 2 / r) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          calc ∑ k : Fin (n * m), |(if s k = 1 then (1 : ℝ) else -1) * G j (x k)|
              ≤ ∑ _k : Fin (n * m), 4 * B1 ^ 2 / r := by
                refine Finset.sum_le_sum (fun k _ => ?_)
                rw [abs_mul]
                have h1 : |(if s k = 1 then (1 : ℝ) else -1)| ≤ 1 := by
                  split_ifs <;> norm_num
                exact le_trans (mul_le_mul h1 (hGbound j (x k)) (abs_nonneg _) zero_le_one)
                  (le_of_eq (one_mul _))
            _ = ((n * m : ℕ) : ℝ) * (4 * B1 ^ 2 / r) := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [abs_mul, abs_of_pos hNinv]
        refine le_trans (mul_le_mul_of_nonneg_left hstep (le_of_lt hNinv)) ?_
        have hcast : ((n * m : ℕ) : ℝ) ≠ 0 := by
          have hpos : (0:ℝ) < ((n * m : ℕ) : ℝ) := by exact_mod_cast hnm
          exact ne_of_gt hpos
        rw [← mul_assoc, inv_mul_cancel₀ hcast, one_mul]
      have hbdd : BddAbove (Set.range fun j : Fin Fs.card =>
          |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
            (if s k = 1 then (1 : ℝ) else -1) * G j (x k)|) := hbddGen _
      have h0 : (0:ℝ) ≤ ⨆ j : Fin Fs.card,
          |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
            (if s k = 1 then (1 : ℝ) else -1) * G j (x k)| :=
        le_trans (abs_nonneg _) (le_ciSup hbdd ⟨0, hFscard⟩)
      rw [abs_of_nonneg h0]
      exact ciSup_le hterm

    have hclip : ∀ x : ℝ, x = 1 ∨ x = -1 → (if x = 1 then (1 : ℝ) else -1) = x := by
      rintro x (rfl | hx)
      · rw [if_pos rfl]
      · rw [hx, if_neg (by norm_num : (-1:ℝ) ≠ 1)]
    have hsmear : ∀ k : Fin (n * m), ∀ᵐ ω ∂P,
        sigma (e.symm k).1 (e.symm k).2 ω = 1 ∨ sigma (e.symm k).1 (e.symm k).2 ω = -1 := by
      intro k
      rw [← MeasureTheory.ae_map_iff (hsm (e.symm k).1 (e.symm k).2).aemeasurable
        (show MeasurableSet {y : ℝ | y = 1 ∨ y = -1} from
          (measurableSet_singleton (1:ℝ)).union (measurableSet_singleton (-1)))]
      rw [hsl (e.symm k).1 (e.symm k).2]
      rw [MeasureTheory.ae_iff]
      simp [rademacherLaw, MeasureTheory.Measure.dirac_apply]
    have hσall : ∀ᵐ ω ∂P, ∀ k : Fin (n * m),
        sigma (e.symm k).1 (e.symm k).2 ω = 1 ∨ sigma (e.symm k).1 (e.symm k).2 ω = -1 := by
      rw [MeasureTheory.ae_all_iff]
      exact hsmear
    have hεm : ∀ k : Fin (n * m), Measurable fun ω => sigma (e.symm k).1 (e.symm k).2 ω :=
      fun k => hsm _ _
    have hεl : ∀ k : Fin (n * m),
        Measure.map (fun ω => sigma (e.symm k).1 (e.symm k).2 ω) P = rademacherLaw :=
      fun k => hsl _ _
    have hεi : iIndepFun (fun k : Fin (n * m) => fun ω => sigma (e.symm k).1 (e.symm k).2 ω) P := by
      have hinj : Function.Injective (fun k : Fin (n * m) => e.symm k) :=
        fun a b hab => e.symm.injective hab
      simpa only using hsi.precomp (g := fun k : Fin (n * m) => e.symm k) hinj
    have hind : IndepFun (fun ω => fun k : Fin (n * m) => sigma (e.symm k).1 (e.symm k).2 ω)
        (fun ω => fun k : Fin (n * m) => Xf k ω) P := by
      have h1 : Measurable fun a : (Fin n × Fin m → ℝ) => fun k : Fin (n * m) => a (e.symm k) :=
        measurable_pi_iff.mpr (fun k => measurable_pi_apply (e.symm k))
      have h2 : Measurable fun a : (Fin n × Fin m → Ωs) => fun k : Fin (n * m) => a (e.symm k) :=
        measurable_pi_iff.mpr (fun k => measurable_pi_apply (e.symm k))
      have h3 := hsX.comp h1 h2
      simpa only [hXf, Function.comp_apply] using h3
    have key2 : Statlib.StatFoundation.Vocabulary.rademacherComplexity (n * m) G P Xf
        = ∫ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 / (predError PX f0 f + r)|) ''
            (Fs : Set (Ωs → ℝ))) ∂P := by
      have hsignU : ∀ b : Bool,
          (if (if b = true then (1 : ℝ) else -1) = 1 then (1 : ℝ) else -1)
            = (if b = true then (1 : ℝ) else -1) := by
        intro b
        exact hclip _ (by
          cases b
          · exact Or.inr (by simp)
          · exact Or.inl (by simp))
      have hA : Statlib.StatFoundation.Vocabulary.rademacherComplexity (n * m) G P Xf
          = ∫ ω, ((Fintype.card (Fin (n * m) → Bool) : ℝ)⁻¹ *
              ∑ s : Fin (n * m) → Bool,
                (fun s x => ⨆ j : Fin Fs.card, |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
                  (if s k = 1 then (1 : ℝ) else -1) * G j (x k)|)
                  (fun k => if s k = true then (1 : ℝ) else -1) (fun k => Xf k ω)) ∂P := by
        simp only [Statlib.StatFoundation.Vocabulary.rademacherComplexity,
          Statlib.StatFoundation.Vocabulary.empiricalRademacherComplexity,
          Statlib.StatFoundation.Vocabulary.rademacherSign, hsignU]
      rw [hA]
      have hchild := statopia_math_node_1903948443_c79ced3a (n * m) hnm P
        (fun k (ω : Ωrand) => sigma (e.symm k).1 (e.symm k).2 ω) Xf hεm hεl hεi hXfm hind
        (fun s x => ⨆ j : Fin Fs.card, |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
          (if s k = 1 then (1 : ℝ) else -1) * G j (x k)|)
        hΦm (4 * B1 ^ 2 / r) hΦC
      rw [hchild]
      have hpt : ∀ ω : Ωrand, (∀ k : Fin (n * m), sigma (e.symm k).1 (e.symm k).2 ω = 1
            ∨ sigma (e.symm k).1 (e.symm k).2 ω = -1) →
          (⨆ j : Fin Fs.card, |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
              (if sigma (e.symm k).1 (e.symm k).2 ω = 1 then (1 : ℝ) else -1) * G j (Xf k ω)|)
            = sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
                sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 / (predError PX f0 f + r)|) ''
                  (Fs : Set (Ωs → ℝ))) := by
        intro ω hω
        rw [hbridge (fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
            sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 / (predError PX f0 f + r)|)
          (fun f hf => abs_nonneg _)]
        haveI : Nonempty (Fin Fs.card) := ⟨⟨0, hFscard⟩⟩
        have hEqj : ∀ j : Fin Fs.card,
            |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j' : Fin m,
                sigma i j' ω * (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2
                  / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)|
              = |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
                  (if sigma (e.symm k).1 (e.symm k).2 ω = 1 then (1 : ℝ) else -1) * G j (Xf k ω)| := by
          intro j
          have hsum : ∑ k : Fin (n * m),
                (if sigma (e.symm k).1 (e.symm k).2 ω = 1 then (1 : ℝ) else -1) * G j (Xf k ω)
              = ∑ i : Fin n, ∑ j' : Fin m,
                  sigma i j' ω * (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2
                    / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r) := by
            have h1 : ∑ k : Fin (n * m),
                  (if sigma (e.symm k).1 (e.symm k).2 ω = 1 then (1 : ℝ) else -1) * G j (Xf k ω)
                = ∑ p : Fin n × Fin m,
                    (if sigma p.1 p.2 ω = 1 then (1 : ℝ) else -1) * G j (X p.1 p.2 ω) := by
              simp only [hXf]
              rw [Equiv.sum_comp e.symm (fun p : Fin n × Fin m =>
                (if sigma p.1 p.2 ω = 1 then (1 : ℝ) else -1) * G j (X p.1 p.2 ω))]
            rw [h1, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j' _ => ?_))
            have hω' : sigma i j' ω = 1 ∨ sigma i j' ω = -1 := by
              simpa using hω (e (i, j'))
            rw [hclip (sigma i j' ω) hω']
            simp only [hG]
            ring
          rw [hsum, Nat.cast_mul]
        refine le_antisymm ?_ ?_
        · refine ciSup_le (fun j => ?_)
          rw [← hEqj j]
          exact le_ciSup (f := fun j => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j' : Fin m,
            sigma i j' ω * (((eF.symm j : ↥Fs) : Ωs → ℝ) (X i j' ω) - f0 (X i j' ω)) ^ 2
              / (predError PX f0 ((eF.symm j : ↥Fs) : Ωs → ℝ) + r)|) (hbddGen _) j
        · refine ciSup_le (fun j => ?_)
          rw [hEqj j]
          exact le_ciSup (f := fun j => |((n * m : ℕ) : ℝ)⁻¹ * ∑ k : Fin (n * m),
            (if sigma (e.symm k).1 (e.symm k).2 ω = 1 then (1 : ℝ) else -1) * G j (Xf k ω)|)
            (hbddGen _) j
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hσall] with ω hω
      exact hpt ω hω
    have hsym :
        ∫ ω, Statlib.StatFoundation.Vocabulary.uniformDeviation (n * m) G P (Xf ⟨0, hnm⟩)
            (fun k => Xf k ω) ∂P
          ≤ 2 * Statlib.StatFoundation.Vocabulary.rademacherComplexity (n * m) G P Xf :=
      Statlib.StatFoundation.EmpiricalProcess.empirical_symmetrization Ωrand P Ωs (n * m)
        Fs.card hnm hFscard Xf hXfm hXfi hXfid G hGm hint
    have hstep1 : (∫ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
        ((∫ x, (f x - f0 x) ^ 2 ∂PX) - (f (X i j ω) - f0 (X i j ω)) ^ 2) /
          ((∫ x, (f x - f0 x) ^ 2 ∂PX) + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P)
        = ∫ ω, Statlib.StatFoundation.Vocabulary.uniformDeviation (n * m) G P (Xf ⟨0, hnm⟩)
            (fun k => Xf k ω) ∂P := by
      have h := congrArg (fun h : Ωrand → ℝ => ∫ ω, h ω ∂P) key1
      simpa only [predError] using h
    have hstep2 : Statlib.StatFoundation.Vocabulary.rademacherComplexity (n * m) G P Xf
        = ∫ ω, sSup ((fun f : Ωs → ℝ => |((n : ℝ) * (m : ℝ))⁻¹ * ∑ i : Fin n, ∑ j : Fin m,
          sigma i j ω * (f (X i j ω) - f0 (X i j ω)) ^ 2 /
            ((∫ x, (f x - f0 x) ^ 2 ∂PX) + r)|) '' (Fs : Set (Ωs → ℝ))) ∂P := by
      simpa only [predError] using key2
    rw [hstep1]
    refine le_trans hsym ?_
    rw [hstep2]
  /- @proof-region region.target-node.session.cb0a2cba48aff83e end -/

end

end Statlib.Imported

