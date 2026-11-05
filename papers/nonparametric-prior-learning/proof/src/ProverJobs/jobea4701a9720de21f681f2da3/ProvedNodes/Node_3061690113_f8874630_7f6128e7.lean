import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_224186213_92110505_fef9b631
import ProverJobs.jobea4701a9720de21f681f2da3.ProvedNodes.Node_4070022191_35653aaa_40321128
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
open Statlib.Imported
open Statlib.Imported.T24
open T24

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace Statlib.Imported
noncomputable section
open T24

set_option autoImplicit false in
theorem statopia_math_node_3061690113_f8874630 : ∀ {U : Type*} [MeasurableSpace U] (n : ℕ)
    (kap lam : Fin n → Measure U)
    (hkap_prob : ∀ i : Fin n, IsProbabilityMeasure (kap i))
    (hlam_prob : ∀ i : Fin n, IsProbabilityMeasure (lam i)),
    InformationTheory.klDiv (Measure.pi kap) (Measure.pi lam)
      = ∑ i : Fin n, InformationTheory.klDiv (kap i) (lam i) := by
  /- @proof-region region.target-node.session.9a05b18b5f1720d0 begin -/
  intro U _ n kap lam hkap_prob hlam_prob
  by_cases hac : Measure.pi kap ≪ Measure.pi lam
  · have hiff : ∀ i : Fin n, kap i ≪ lam i :=
      (statopia_math_node_224186213_92110505 n kap lam hkap_prob hlam_prob).mp hac
    exact statopia_math_node_4070022191_35653aaa n kap lam hkap_prob hlam_prob hiff
  · have hnot : ¬ ∀ i : Fin n, kap i ≪ lam i := fun h =>
      hac ((statopia_math_node_224186213_92110505 n kap lam hkap_prob hlam_prob).mpr h)
    push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    have hL : InformationTheory.klDiv (Measure.pi kap) (Measure.pi lam) = ⊤ :=
      InformationTheory.klDiv_of_not_ac hac
    have htop : InformationTheory.klDiv (kap i) (lam i) = ⊤ :=
      InformationTheory.klDiv_of_not_ac hi
    have hle : (⊤ : ℝ≥0∞) ≤ ∑ j : Fin n, InformationTheory.klDiv (kap j) (lam j) := by
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun j : Fin n => InformationTheory.klDiv (kap j) (lam j))
        (fun j _ => zero_le _) (Finset.mem_univ i))
      simp only [htop]
      exact le_rfl
    rw [hL]
    exact le_antisymm hle le_top
  /- @proof-region region.target-node.session.9a05b18b5f1720d0 end -/

end
end Statlib.Imported
