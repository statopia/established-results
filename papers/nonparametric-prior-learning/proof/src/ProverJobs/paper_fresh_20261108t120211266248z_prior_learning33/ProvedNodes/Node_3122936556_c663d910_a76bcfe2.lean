import Lean
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Vocabulary
import ProverJobs.paper_fresh_20261108t120211266248z_prior_learning33.Base

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
theorem statopia_math_node_3122936556_c663d910 : ∀ (X : Type*) [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    (H : Type*) [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (nrm : H → ℝ≥0∞) (ok : H → Prop)
    (m : ℕ) (hm : 0 < m) (S : Fin m → X × H) (y : H)
    (Z : Type*) [TopologicalSpace Z] (L : Z) (g : (Fin m → X × H) → Z),
    let scaleNhds : H → Filter H := fun c =>
      ⨅ ε : { ε : ℝ // 0 < ε },
        Filter.principal { z : H | ok z ∧ nrm (z - c) < ENNReal.ofReal ε }
    let dataNhds : (Fin m → X × H) → Filter (Fin m → X × H) := fun T =>
      ⨅ j : Fin m, Filter.comap (fun S' => (S' j).1) (𝓝 (T j).1) ⊓
        Filter.comap (fun S' => (S' j).2) (scaleNhds (T j).2)
    (scaleNhds y
        = ⨅ n : ℕ, Filter.principal
            { z : H | ok z ∧ nrm (z - y) < ENNReal.ofReal (1 / ((n : ℝ) + 1))}) ∧
      (∃ B : ℕ → Set (Fin m → X × H),
          dataNhds S = ⨅ n : ℕ, Filter.principal (B n) ∧
            ∀ n : ℕ, B (n + 1) ⊆ B n) ∧
        ((∀ D : ℕ → (Fin m → X × H),
            Tendsto D Filter.atTop (dataNhds S) →
              Tendsto (fun n => g (D n)) Filter.atTop (𝓝 L)) →
          Tendsto g (dataNhds S) (𝓝 L)) := by
  /- @proof-region region.target-node.session.0183d85793326c0b begin -/
  intro X _ _ H _ _ _ nrm ok m hm S y Z _ L g
  dsimp only
  have hA : ∀ c : H,
      (⨅ ε : { ε : ℝ // 0 < ε }, Filter.principal { z : H | ok z ∧ nrm (z - c) < ENNReal.ofReal (ε : ℝ) })
        = ⨅ n : ℕ, Filter.principal { z : H | ok z ∧ nrm (z - c) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) } := by
    intro c
    apply le_antisymm
    · refine le_iInf fun n => ?_
      exact iInf_le (fun ε : { ε : ℝ // 0 < ε } => Filter.principal { z : H | ok z ∧ nrm (z - c) < ENNReal.ofReal (ε : ℝ) }) ⟨1 / ((n : ℝ) + 1), by positivity⟩
    · refine le_iInf fun ε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt ε.2
      refine le_trans (iInf_le (fun n : ℕ => Filter.principal { z : H | ok z ∧ nrm (z - c) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }) n) ?_
      refine Filter.principal_mono.mpr ?_
      intro z hz
      exact ⟨hz.1, lt_of_lt_of_le hz.2 (ENNReal.ofReal_le_ofReal (le_of_lt hn))⟩
  have hfac1 : ∀ j : Fin m,
      Filter.comap (fun S' : Fin m → X × H => (S' j).1) (𝓝 (S j).1)
        = ⨅ n : ℕ, Filter.principal { S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } := by
    intro j
    rw [(Metric.nhds_basis_ball_inv_nat_succ (x := (S j).1)).eq_iInf, Filter.comap_iInf]
    simp only [Filter.comap_principal]
    rfl
  have hfac2 : ∀ j : Fin m,
      Filter.comap (fun S' : Fin m → X × H => (S' j).2) (⨅ ε : { ε : ℝ // 0 < ε }, Filter.principal { z : H | ok z ∧ nrm (z - (S j).2) < ENNReal.ofReal (ε : ℝ) })
        = ⨅ n : ℕ, Filter.principal { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) } := by
    intro j
    rw [hA (S j).2, Filter.comap_iInf]
    simp only [Filter.comap_principal]
    rfl
  have hB1 : ∀ j : Fin m,
      (⨅ n : ℕ, Filter.principal { S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) })
        ⊓ (⨅ n : ℕ, Filter.principal { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })
        = ⨅ n : ℕ, Filter.principal ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) }
            ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }) := by
    intro j
    have hAb : (⨅ n : ℕ, Filter.principal { S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) }).HasBasis (fun t : Set ℕ => t.Finite) (fun t => ⋂ n ∈ t, { S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) }) :=
      Filter.hasBasis_iInf_principal_finite (fun n : ℕ => { S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) })
    have hCb : (⨅ n : ℕ, Filter.principal { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }).HasBasis (fun t : Set ℕ => t.Finite) (fun t => ⋂ n ∈ t, { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }) :=
      Filter.hasBasis_iInf_principal_finite (fun n : ℕ => { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })
    have hRb : (⨅ n : ℕ, Filter.principal ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })).HasBasis (fun t : Set ℕ => t.Finite) (fun t => ⋂ n ∈ t, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })) :=
      Filter.hasBasis_iInf_principal_finite (fun n : ℕ => ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }))
    apply le_antisymm
    · rw [(hAb.inf hCb).le_basis_iff hRb]
      intro t ht
      exact ⟨(t, t), ⟨ht, ht⟩, fun x hx => by
        simp only [Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
        exact fun n hn => ⟨hx.1 n hn, hx.2 n hn⟩⟩
    · refine le_inf (le_iInf fun n => ?_) (le_iInf fun n => ?_)
      · exact le_trans (iInf_le (fun n : ℕ => Filter.principal ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })) n) (Filter.principal_mono.mpr Set.inter_subset_left)
      · exact le_trans (iInf_le (fun n : ℕ => Filter.principal ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })) n) (Filter.principal_mono.mpr Set.inter_subset_right)
  have hBeq : (⨅ j : Fin m, Filter.comap (fun S' : Fin m → X × H => (S' j).1) (𝓝 (S j).1) ⊓ Filter.comap (fun S' : Fin m → X × H => (S' j).2) (⨅ ε : { ε : ℝ // 0 < ε }, Filter.principal { z : H | ok z ∧ nrm (z - (S j).2) < ENNReal.ofReal (ε : ℝ) }))
      = ⨅ n : ℕ, Filter.principal (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })) := by
    simp only [hfac1, hfac2, hB1]
    apply le_antisymm
    · refine le_iInf fun n => ?_
      rw [Filter.le_principal_iff]
      have hb : (⨅ j : Fin m, ⨅ k : ℕ, Filter.principal ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((k : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) })).HasBasis
          (fun If : Σ (s : Set (Fin m)), (i : ↑s) → Set ℕ => If.1.Finite ∧ ∀ i, (If.2 i).Finite)
          (fun If => ⋂ i, ⋂ k ∈ If.2 i, ({ S' : Fin m → X × H | (S' (↑i)).1 ∈ Metric.ball (S (↑i)).1 (1 / ((k : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' (↑i)).2) ∧ nrm ((S' (↑i)).2 - (S (↑i)).2) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) })) :=
        Filter.HasBasis.iInf (fun j => Filter.hasBasis_iInf_principal_finite (fun k : ℕ => ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((k : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) })))
      rw [hb.mem_iff]
      refine ⟨⟨Set.univ, fun _ => {n}⟩, ⟨?_, ?_⟩, ?_⟩
      · simp
      · intro i
        simp
      · intro x hx
        simp only [Set.mem_iInter] at hx ⊢
        intro j
        exact hx ⟨j, trivial⟩ n rfl
    · refine le_iInf fun j => le_iInf fun n => ?_
      exact le_trans (iInf_le (fun k : ℕ => Filter.principal (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((k : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) }))) n) (Filter.principal_mono.mpr (Set.iInter_subset (fun j : Fin m => ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })) j))
  have hBsub : ∀ {a b : ℕ}, a ≤ b → (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((b : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((b : ℝ) + 1)) })) ⊆ (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((a : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((a : ℝ) + 1)) })) := by
    intro a b hab
    have hrad : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
      have h1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have h2 : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
        have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith
      exact one_div_le_one_div_of_le h1 h2
    refine Set.iInter_mono fun j => Set.inter_subset_inter ?_ ?_
    · intro x hx
      exact Metric.ball_subset_ball hrad hx
    · intro x hx
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (ENNReal.ofReal_le_ofReal hrad)⟩
  refine ⟨hA y, ⟨fun n => ⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }), hBeq, ?_⟩, ?_⟩
  · intro n
    exact hBsub (a := n) (b := n + 1) (le_of_lt (Nat.lt_succ_self n))
  · intro hseq
    by_contra hcon
    have hmap : ¬ (Filter.map g (⨅ j : Fin m, Filter.comap (fun S' : Fin m → X × H => (S' j).1) (𝓝 (S j).1) ⊓ Filter.comap (fun S' : Fin m → X × H => (S' j).2) (⨅ ε : { ε : ℝ // 0 < ε }, Filter.principal { z : H | ok z ∧ nrm (z - (S j).2) < ENNReal.ofReal (ε : ℝ) })) ≤ 𝓝 L) := hcon
    have hex : ∃ V : Set Z, V ∈ 𝓝 L ∧ g ⁻¹' V ∉ (⨅ j : Fin m, Filter.comap (fun S' : Fin m → X × H => (S' j).1) (𝓝 (S j).1) ⊓ Filter.comap (fun S' : Fin m → X × H => (S' j).2) (⨅ ε : { ε : ℝ // 0 < ε }, Filter.principal { z : H | ok z ∧ nrm (z - (S j).2) < ENNReal.ofReal (ε : ℝ) })) := by
      by_contra h
      push_neg at h
      exact hmap (fun s hs => Filter.mem_map.mpr (h s hs))
    obtain ⟨V, hV, hVl⟩ := hex
    have hexB : ∀ n : ℕ, ∃ x : Fin m → X × H, x ∈ (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) })) ∧ g x ∉ V := by
      intro n
      by_contra h
      push_neg at h
      have hmem : g ⁻¹' V ∈ (⨅ n : ℕ, Filter.principal (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }))) := by
        refine (Filter.le_principal_iff).mp (le_trans (iInf_le (fun n : ℕ => Filter.principal (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }))) n) (Filter.principal_mono.mpr (fun x hx => h x hx)))
      rw [← hBeq] at hmem
      exact hVl hmem
    choose D hD1 hD2 using hexB
    have hDtend : Tendsto D atTop (⨅ j : Fin m, Filter.comap (fun S' : Fin m → X × H => (S' j).1) (𝓝 (S j).1) ⊓ Filter.comap (fun S' : Fin m → X × H => (S' j).2) (⨅ ε : { ε : ℝ // 0 < ε }, Filter.principal { z : H | ok z ∧ nrm (z - (S j).2) < ENNReal.ofReal (ε : ℝ) })) := by
      rw [hBeq]
      show Filter.map D atTop ≤ ⨅ n : ℕ, Filter.principal (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }))
      refine le_iInf fun n => ?_
      rw [Filter.le_principal_iff]
      show ∀ᶠ k : ℕ in atTop, D k ∈ (⋂ j : Fin m, ({ S' : Fin m → X × H | (S' j).1 ∈ Metric.ball (S j).1 (1 / ((n : ℝ) + 1)) } ∩ { S' : Fin m → X × H | ok ((S' j).2) ∧ nrm ((S' j).2 - (S j).2) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) }))
      rw [Filter.eventually_atTop]
      exact ⟨n, fun k hk => hBsub hk (hD1 k)⟩
    have hev : ∀ᶠ n : ℕ in atTop, g (D n) ∈ V := (hseq D hDtend).eventually hV
    obtain ⟨a, ha⟩ := (Filter.eventually_atTop).mp hev
    exact hD2 a (ha a le_rfl)
  /- @proof-region region.target-node.session.0183d85793326c0b end -/

end Statlib.Imported
end

