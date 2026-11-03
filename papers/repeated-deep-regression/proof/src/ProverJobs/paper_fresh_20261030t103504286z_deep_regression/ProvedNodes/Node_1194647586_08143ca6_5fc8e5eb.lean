import Lean
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Vocabulary
import ProverJobs.paper_fresh_20261030t103504286z_deep_regression.Base

namespace PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.paper_fresh_20261030t103504286z_deep_regression.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1194647586_08143ca6 : ∀ {Ω ΩS : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩS]
    (mu : Measure ΩS) [IsProbabilityMeasure mu] (PX : Measure Ω)
    (n m : ℕ) (F : Set (Ω → ℝ)) (f0 : Ω → ℝ)
    (X : Fin n → Fin m → ΩS → Ω) (sigma : Fin n → Fin m → ΩS → ℝ) (B1 : ℝ)
    (hB1_pos : 0 < B1)
    (hX_meas : ∀ (i : Fin n) (j : Fin m), Measurable (X i j))
    (hsigma_meas : ∀ (i : Fin n) (j : Fin m), Measurable (sigma i j))
    (hsigma_law : ∀ p : Fin n × Fin m,
      Measure.map (sigma p.1 p.2) mu = rademacherLaw)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hf0_meas : Measurable f0)
    (hf0_bound : ∀ x : Ω, |f0 x| ≤ B1)
    (hF_bound : ∀ f ∈ F, ∀ x : Ω, |f x| ≤ B1),
    ∀ (r : ℝ) (Fs : Finset (Ω → ℝ)),
      (Fs : Set (Ω → ℝ)) ⊆ localized PX F f0 r →
      Integrable (fun ω : ΩS =>
        rademacherFiniteSup (fun p : Fin n × Fin m => X p.1 p.2) f0
          (fun p : Fin n × Fin m => sigma p.1 p.2) ω Fs) mu := by
  /- @proof-region region.target-node.session.27a703548cf43689 begin -/
  intro Ω ΩS _ _ mu _ PX n m F f0 X sigma B1 hB1 hX_meas hsigma_meas hsigma_law
    hF_meas hf0_meas hf0_bound hF_bound r Fs hFs_sub
  by_cases hFs : Fs.Nonempty
  · have hbridge : (fun ω : ΩS =>
        rademacherFiniteSup (fun ij : Fin n × Fin m => X ij.1 ij.2) f0
          (fun ij : Fin n × Fin m => sigma ij.1 ij.2) ω Fs)
        = Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
          |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
            sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|) := by
      funext ω
      simp only [rademacherFiniteSup, ← sSup_range]
      have hT : (0 : ℝ) ≤ (Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
            |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
              sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)) ω := by
        have h₂ : |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
              sigma ij.1 ij.2 ω * (hFs.choose (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| ≤
            (Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
              |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)) ω :=
          (Finset.le_sup' (fun f : Ω → ℝ => fun ω : ΩS =>
            |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
              sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|) hFs.choose_spec) ω
        exact le_trans (abs_nonneg _) h₂
      refine le_antisymm ?_ ?_
      · refine Real.sSup_le ?_ hT
        rintro x ⟨f, rfl⟩
        refine Real.sSup_le ?_ hT
        rintro y ⟨hf, rfl⟩
        exact (Finset.le_sup' (fun f : Ω → ℝ => fun ω : ΩS =>
          |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
            sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)
          (Finset.mem_coe.mp hf)) ω
      · refine Finset.sup'_mem {a : ΩS → ℝ | a ω ≤ sSup (Set.range (fun f : Ω → ℝ =>
            sSup (Set.range (fun _ : f ∈ (Fs : Set (Ω → ℝ)) =>
              |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|))))} ?_ Fs hFs _ ?_
        · intro x hx y hy
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          exact sup_le hx hy
        · intro p hp
          simp only [Set.mem_setOf_eq]
          have h1 : |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| ≤
              sSup (Set.range (fun _ : p ∈ (Fs : Set (Ω → ℝ)) =>
                |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                  sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)) := by
            refine le_csSup ?_ ⟨Finset.mem_coe.mpr hp, rfl⟩
            exact ⟨_, fun y hy => by obtain ⟨-, rfl⟩ := hy; exact le_rfl⟩
          refine le_trans h1 ?_
          refine le_csSup ?_ ⟨p, rfl⟩
          exact ⟨_, fun y hy => by
            obtain ⟨f, rfl⟩ := hy
            refine Real.sSup_le ?_ hT
            rintro z ⟨hz, rfl⟩
            exact (Finset.le_sup' (fun f : Ω → ℝ => fun ω : ΩS =>
              |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)
              (Finset.mem_coe.mp hz)) ω⟩
    rw [hbridge]
    refine MeasureTheory.Integrable.of_bound ?_ (2 * B1) ?_
    · have hmeas : ∀ f ∈ Fs, Measurable (fun ω : ΩS =>
          |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
            sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|) := by
        intro f hf
        have hfF : f ∈ F := (hFs_sub (Finset.mem_coe.mpr hf)).1
        have hfm : Measurable f := hF_meas f hfF
        have hterm : ∀ ij : Fin n × Fin m, Measurable (fun ω : ΩS =>
            sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))) := by
          intro ij
          exact (hsigma_meas ij.1 ij.2).mul
            ((hfm.comp (hX_meas ij.1 ij.2)).sub (hf0_meas.comp (hX_meas ij.1 ij.2)))
        have hsum : Measurable (fun ω : ΩS => ∑ ij : Fin n × Fin m,
            sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))) := by
          apply Finset.measurable_sum
          intro ij _
          exact hterm ij
        exact (hsum.const_mul (1 / ((n : ℝ) * (m : ℝ)))).abs
      have hms : Measurable (Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
          |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
            sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)) :=
        Finset.measurable_sup' hFs hmeas
      exact hms.aestronglyMeasurable
    · have hσ' : ∀ᵐ ω ∂mu, ∀ i : Fin n, ∀ j : Fin m,
          (-1 : ℝ) ≤ sigma i j ω ∧ sigma i j ω ≤ 1 := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        rw [MeasureTheory.ae_all_iff]
        intro j
        rw [← MeasureTheory.ae_map_iff (hsigma_meas i j).aemeasurable
          (p := fun y : ℝ => (-1 : ℝ) ≤ y ∧ y ≤ 1)
          (measurableSet_Icc : MeasurableSet (Set.Icc (-1 : ℝ) 1))]
        rw [hsigma_law (i, j)]
        have h1 : ¬ ((1 : ℝ) < -1) := by norm_num
        have h2 : (-1 : ℝ) ≤ 1 := by norm_num
        rw [MeasureTheory.ae_iff]
        simp [rademacherLaw, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.add_apply,
          MeasureTheory.Measure.dirac_apply, Set.indicator, h1, h2]

      have hσae : ∀ᵐ ω ∂mu, ∀ i : Fin n, ∀ j : Fin m, |sigma i j ω| ≤ 1 := by
        filter_upwards [hσ'] with ω hω i j
        exact abs_le.mpr (hω i j)
      filter_upwards [hσae] with ω hω
      have hle : (Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
            |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
              sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)) ω ≤ 2 * B1 := by
        have hmem : Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
              |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|) ∈
            {a : ΩS → ℝ | a ω ≤ 2 * B1} := by
          refine Finset.sup'_mem _ ?_ Fs hFs _ ?_
          · intro x hx y hy
            simp only [Set.mem_setOf_eq] at hx hy ⊢
            exact sup_le hx hy
          · intro p hp
            simp only [Set.mem_setOf_eq]
            have hpF : p ∈ F := (hFs_sub (Finset.mem_coe.mpr hp)).1
            have hpb : ∀ x : Ω, |p x| ≤ B1 := hF_bound p hpF
            have hterm : ∀ ij : Fin n × Fin m,
                |sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| ≤ 2 * B1 := by
              intro ij
              have hdiff : |p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω)| ≤ 2 * B1 := by
                have hpa := abs_le.mp (hpb (X ij.1 ij.2 ω))
                have hfa := abs_le.mp (hf0_bound (X ij.1 ij.2 ω))
                rw [abs_le]
                constructor <;> linarith [hpa.1, hpa.2, hfa.1, hfa.2]
              calc |sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|
                  = |sigma ij.1 ij.2 ω| * |p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω)| := abs_mul _ _
                _ ≤ 1 * (2 * B1) :=
                    mul_le_mul (hω ij.1 ij.2) hdiff (abs_nonneg _) zero_le_one
                _ = 2 * B1 := by ring
            have hsum : |∑ ij : Fin n × Fin m,
                  sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| ≤
                (n : ℝ) * (m : ℝ) * (2 * B1) := by
              calc |∑ ij : Fin n × Fin m,
                    sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|
                  ≤ ∑ ij : Fin n × Fin m,
                      |sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ ij : Fin n × Fin m, (2 * B1) := by
                    apply Finset.sum_le_sum
                    intro ij _
                    exact hterm ij
                _ = (n : ℝ) * (m : ℝ) * (2 * B1) := by
                    rw [Finset.sum_const]
                    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
                      nsmul_eq_mul, Nat.cast_mul]
            rcases eq_or_ne ((n : ℝ) * (m : ℝ)) 0 with hnm | hnm
            · have hS0 : ∑ ij : Fin n × Fin m,
                  sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω)) = 0 := by
                have hbS := hsum
                rw [hnm, zero_mul] at hbS
                exact abs_eq_zero.mp (le_antisymm hbS (abs_nonneg _))
              rw [hS0, mul_zero, abs_zero]
              linarith
            · have hpos : (0 : ℝ) < (n : ℝ) * (m : ℝ) :=
                lt_of_le_of_ne (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)) (Ne.symm hnm)
              have hc : 1 / ((n : ℝ) * (m : ℝ)) * ((n : ℝ) * (m : ℝ)) = 1 := by
                rw [one_div, inv_mul_cancel₀ (ne_of_gt hpos)]
              calc |1 / ((n : ℝ) * (m : ℝ)) * ∑ ij : Fin n × Fin m,
                    sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|
                  = |1 / ((n : ℝ) * (m : ℝ))| *
                      |∑ ij : Fin n × Fin m,
                        sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| := abs_mul _ _
                _ = (1 / ((n : ℝ) * (m : ℝ))) *
                      |∑ ij : Fin n × Fin m,
                        sigma ij.1 ij.2 ω * (p (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| := by
                    rw [abs_of_pos (by positivity)]
                _ ≤ (1 / ((n : ℝ) * (m : ℝ))) * ((n : ℝ) * (m : ℝ) * (2 * B1)) :=
                    mul_le_mul_of_nonneg_left hsum (le_of_lt (by positivity))
                _ = 2 * B1 := by rw [← mul_assoc, hc, one_mul]
        simpa only [Set.mem_setOf_eq] using hmem
      have h0 : 0 ≤ (Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
            |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
              sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)) ω := by
        have h₂ : |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
              sigma ij.1 ij.2 ω * (hFs.choose (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))| ≤
            (Fs.sup' hFs (fun f : Ω → ℝ => fun ω : ΩS =>
              |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
                sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|)) ω :=
          (Finset.le_sup' (fun f : Ω → ℝ => fun ω : ΩS =>
            |(1 / ((n : ℝ) * (m : ℝ))) * ∑ ij : Fin n × Fin m,
              sigma ij.1 ij.2 ω * (f (X ij.1 ij.2 ω) - f0 (X ij.1 ij.2 ω))|) hFs.choose_spec) ω
        exact le_trans (abs_nonneg _) h₂
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hle
  · have hzero : (fun ω : ΩS =>
        rademacherFiniteSup (fun ij : Fin n × Fin m => X ij.1 ij.2) f0
          (fun ij : Fin n × Fin m => sigma ij.1 ij.2) ω Fs) = fun _ => (0 : ℝ) := by
      funext ω
      simp only [rademacherFiniteSup, ← sSup_range]
      refine le_antisymm ?_ ?_
      · refine Real.sSup_le ?_ le_rfl
        rintro x ⟨f, rfl⟩
        refine Real.sSup_le ?_ le_rfl
        rintro y ⟨hf, -⟩
        exact absurd ⟨f, Finset.mem_coe.mp hf⟩ hFs
      · refine Real.sSup_nonneg ?_
        rintro x ⟨f, rfl⟩
        exact Real.sSup_nonneg (fun y hy => by
          obtain ⟨hf, -⟩ := hy
          exact absurd ⟨f, Finset.mem_coe.mp hf⟩ hFs)
    rw [hzero]
    exact integrable_zero ΩS ℝ mu

  /- @proof-region region.target-node.session.27a703548cf43689 end -/

end Statlib.Imported
end

