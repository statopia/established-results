import ProverJobs.job_paper_383d12cb48d74c8f98648c6beef78bb3.Base

open MeasureTheory

namespace PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3.Statlib.Imported

theorem expectedSup_nonneg {Ω F : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : F → Ω → ℝ) (hV : ∀ f ω, 0 ≤ V f ω) :
    0 ≤ expectedSup μ V := by
  apply Real.sSup_nonneg
  rintro _ ⟨s, rfl⟩
  apply integral_nonneg
  intro ω
  obtain ⟨f, hf⟩ := s.2
  exact le_trans (hV f ω) (Finset.le_sup' (fun f => V f ω) hf)

theorem expectedSup_restrict_le {Ω F : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : F → Ω → ℝ) (C : ℝ) (hV : ∀ f ω, 0 ≤ V f ω ∧ V f ω ≤ C)
    (s : Set F) : expectedSup μ (fun f : s => V f.1) ≤ expectedSup μ V := by
  classical
  have hbdd : BddAbove (Set.range fun q : {q : Finset F // q.Nonempty} =>
      ∫ ω, q.1.sup' q.2 (fun f => V f ω) ∂μ) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨q, rfl⟩
    have hle := integral_mono_of_nonneg (μ := μ)
      (f := fun ω => q.1.sup' q.2 (fun f => V f ω))
      (Filter.Eventually.of_forall fun ω => by
        obtain ⟨f, hf⟩ := q.2
        exact le_trans (hV f ω).1 (Finset.le_sup' (fun f => V f ω) hf))
      (integrable_const C)
      (Filter.Eventually.of_forall fun ω =>
        (Finset.sup'_le_iff q.2 _).mpr fun f _ => (hV f ω).2)
    simpa using hle
  change sSup (Set.range fun q : {q : Finset s // q.Nonempty} =>
      ∫ ω, q.1.sup' q.2 (fun f => V f.1 ω) ∂μ) ≤ expectedSup μ V
  refine Real.sSup_le ?_ (expectedSup_nonneg μ V (fun f ω => (hV f ω).1))
  rintro _ ⟨q, rfl⟩
  let image : Finset F := q.1.image Subtype.val
  have himage : image.Nonempty := q.2.image Subtype.val
  have heq : (fun ω => q.1.sup' q.2 (fun f => V f.1 ω)) =
      (fun ω => image.sup' himage (fun f => V f ω)) := by
    funext ω
    exact Finset.sup'_comp_eq_image q.2 (fun f => V f ω)
  change (∫ ω, q.1.sup' q.2 (fun f => V f.1 ω) ∂μ) ≤ expectedSup μ V
  rw [heq]
  exact le_csSup hbdd (Set.mem_range_self (⟨image, himage⟩ : {q : Finset F // q.Nonempty}))

end PaperProofTasks.job_paper_383d12cb48d74c8f98648c6beef78bb3.Statlib.Imported
