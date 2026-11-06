import Lean
import ProverJobs.ResidualE2ESupport20261106.M_fa8bbc31a4e4e2df874d

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ResidualLoss20261106
universe u

theorem sum_independence {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι : Type*} [Fintype ι] (X Y : Ω → ι → ℝ)
    (hX : ∀ i, Measurable fun ω => X ω i)
    (hY : ∀ i, Measurable fun ω => Y ω i)
    (h : iIndepFun (fun k : ι ⊕ ι => fun ω => Sum.elim (Y ω) (X ω) k) μ) :
    iIndepFun (fun i ω => X ω i) μ ∧
    iIndepFun (fun i ω => Y ω i) μ ∧ IndepFun X Y μ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact h.precomp Sum.inr_injective
  · exact h.precomp Sum.inl_injective
  · let S : Finset (ι ⊕ ι) := Finset.univ.image Sum.inr
    let T : Finset (ι ⊕ ι) := Finset.univ.image Sum.inl
    have hd : Disjoint S T := by
      simp only [S, T, Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
      rintro k ⟨i, rfl⟩ ⟨j, hj⟩
      cases hj
    have hm : ∀ k : ι ⊕ ι, Measurable (fun ω => Sum.elim (Y ω) (X ω) k) := by
      intro k
      cases k with
      | inl i => exact hY i
      | inr i => exact hX i
    have hi := h.indepFun_finset S T hd hm
    let ex : ι → S := fun i => ⟨Sum.inr i, by simp [S]⟩
    let ey : ι → T := fun i => ⟨Sum.inl i, by simp [T]⟩
    have hx : Measurable (fun z : S → ℝ => fun i => z (ex i)) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply (ex i)
    have hy : Measurable (fun z : T → ℝ => fun i => z (ey i)) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply (ey i)
    exact hi.comp hx hy
end ResidualLoss20261106

#print axioms ResidualLoss20261106.sum_independence

