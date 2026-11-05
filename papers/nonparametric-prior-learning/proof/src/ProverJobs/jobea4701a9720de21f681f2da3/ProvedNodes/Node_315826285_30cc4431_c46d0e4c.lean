import ProverJobs.jobea4701a9720de21f681f2da3.Vocabulary
import ProverJobs.jobea4701a9720de21f681f2da3.Base

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
theorem statopia_math_node_315826285_30cc4431 : ∀ {U : Type*} [MeasurableSpace U] (n : ℕ)
    (lam : Fin n → Measure U) (hlam : ∀ i : Fin n, IsProbabilityMeasure (lam i))
    (f : Fin n → U → ℝ≥0∞) (hf : ∀ i : Fin n, Measurable (f i)),
    ∫⁻ u : (Fin n → U), (∏ i : Fin n, f i (u i)) ∂(Measure.pi lam) =
      ∏ i : Fin n, ∫⁻ x : U, f i x ∂(lam i) := by
  /- @proof-region region.target-node.session.a2db66d0e472df00 begin -/
  intro U _ n
  induction n with
  | zero =>
      intro lam hlam f hf
      simp
  | succ m ih =>
      intro lam hlam f hf
      have key :
          ∫⁻ u : Fin (m + 1) → U, (∏ i : Fin (m + 1), f i (u i)) ∂(Measure.pi lam) =
            (∫⁻ x : U, f 0 x ∂(lam 0)) *
              (∫⁻ v : Fin m → U, (∏ j : Fin m, f j.succ (v j))
                ∂(Measure.pi (fun j : Fin m => lam j.succ))) := by
        have hF_meas :
            Measurable (fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U)) := by
          rw [measurable_pi_iff]
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa [Fin.cons_zero] using measurable_fst
          · simpa [Fin.cons_succ] using (measurable_pi_apply j).comp measurable_snd
        have hg_meas : Measurable fun u : Fin (m + 1) → U => ∏ i : Fin (m + 1), f i (u i) :=
          Finset.measurable_prod Finset.univ (fun i _ => (hf i).comp (measurable_pi_apply i))
        have hdec :
            Measure.map (fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U))
                ((lam 0).prod (Measure.pi (fun j : Fin m => lam j.succ))) = Measure.pi lam := by
          refine (Measure.pi_eq (μ := lam)
            (μ' := Measure.map (fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U))
              ((lam 0).prod (Measure.pi (fun j : Fin m => lam j.succ)))) ?_).symm
          intro s hs
          have hpre :
              (fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U)) ⁻¹' (Set.univ.pi s)
                = s 0 ×ˢ (Set.univ.pi fun j : Fin m => s j.succ) := by
            ext p
            constructor
            · intro hp
              exact ⟨by simpa [Fin.cons_zero] using (Set.mem_univ_pi.mp hp) 0,
                fun j => by simpa [Fin.cons_succ] using (Set.mem_univ_pi.mp hp) j.succ⟩
            · intro hp i
              refine Fin.cases ?_ (fun j => ?_) i
              · simpa [Fin.cons_zero] using hp.1
              · simpa [Fin.cons_succ] using (Set.mem_univ_pi.mp hp.2) j
          have hms : MeasurableSet (Set.univ.pi s) := by
            have hEq : Set.univ.pi s
                = ⋂ i, (fun u : Fin (m + 1) → U => u i) ⁻¹' (s i) := by
              ext u
              simp [Set.mem_univ_pi]
            rw [hEq]
            exact MeasurableSet.iInter (fun i => (hs i).preimage (measurable_pi_apply i))
          rw [Measure.map_apply hF_meas hms, hpre, Measure.prod_prod, Measure.pi_pi]
          rw [Fin.prod_univ_succ]
        have hmap1 :
            (∫⁻ b : Fin (m + 1) → U, (∏ i : Fin (m + 1), f i (b i))
                ∂(Measure.map (fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U))
                  ((lam 0).prod (Measure.pi (fun j : Fin m => lam j.succ))))) =
              ∫⁻ p : U × (Fin m → U),
                (∏ i : Fin (m + 1),
                  f i ((fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U)) p i))
                ∂((lam 0).prod (Measure.pi (fun j : Fin m => lam j.succ))) :=
          MeasureTheory.lintegral_map hg_meas hF_meas
        have hpt : ∀ p : U × (Fin m → U),
            (∏ i : Fin (m + 1),
                f i ((fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U)) p i)) =
              f 0 p.1 * ∏ j : Fin m, f j.succ (p.2 j) := by
          intro p
          rw [Fin.prod_univ_succ]
          simp [Fin.cons_zero, Fin.cons_succ]
        have hm : Measurable fun v : Fin m → U => ∏ j : Fin m, f j.succ (v j) :=
          Finset.measurable_prod Finset.univ (fun j _ => (hf j.succ).comp (measurable_pi_apply j))
        have hprod := MeasureTheory.lintegral_prod_mul (μ := lam 0)
          (ν := Measure.pi (fun j : Fin m => lam j.succ))
          (f := fun x : U => f 0 x)
          (g := fun v : Fin m → U => ∏ j : Fin m, f j.succ (v j))
          (hf 0).aemeasurable hm.aemeasurable
        calc ∫⁻ u : Fin (m + 1) → U, (∏ i : Fin (m + 1), f i (u i)) ∂(Measure.pi lam)
            = ∫⁻ b : Fin (m + 1) → U, (∏ i : Fin (m + 1), f i (b i))
                ∂(Measure.map (fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U))
                  ((lam 0).prod (Measure.pi (fun j : Fin m => lam j.succ)))) := by rw [hdec]
          _ = ∫⁻ p : U × (Fin m → U),
                (∏ i : Fin (m + 1),
                  f i ((fun p : U × (Fin m → U) => (Fin.cons p.1 p.2 : Fin (m + 1) → U)) p i))
                ∂((lam 0).prod (Measure.pi (fun j : Fin m => lam j.succ))) := hmap1
          _ = ∫⁻ p : U × (Fin m → U), f 0 p.1 * (∏ j : Fin m, f j.succ (p.2 j))
                ∂((lam 0).prod (Measure.pi (fun j : Fin m => lam j.succ))) :=
              lintegral_congr fun p => hpt p
          _ = (∫⁻ x : U, f 0 x ∂(lam 0)) *
                (∫⁻ v : Fin m → U, (∏ j : Fin m, f j.succ (v j))
                  ∂(Measure.pi (fun j : Fin m => lam j.succ))) := hprod
      have h2 := ih (fun j : Fin m => lam j.succ) (fun j : Fin m => hlam j.succ)
        (fun j : Fin m => f j.succ) (fun j : Fin m => hf j.succ)
      have h2' :
          (∫⁻ v : Fin m → U, (∏ j : Fin m, f j.succ (v j))
              ∂(Measure.pi (fun j : Fin m => lam j.succ))) =
            ∏ j : Fin m, ∫⁻ x : U, f j.succ x ∂(lam j.succ) := h2
      rw [key, h2', Fin.prod_univ_succ]
  /- @proof-region region.target-node.session.a2db66d0e472df00 end -/

end
end Statlib.Imported
