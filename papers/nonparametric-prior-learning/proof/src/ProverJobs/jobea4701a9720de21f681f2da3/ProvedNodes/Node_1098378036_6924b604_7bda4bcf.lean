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
theorem statopia_math_node_1098378036_6924b604 : ∀ (Ω : Type*) [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (ν : ProbabilityMeasure Ω) (g : Ω → ℝ) (hg : Measurable g),
    Filter.Tendsto
      (fun n : ℕ =>
        ENNReal.toEReal
          (∫⁻ x, ENNReal.ofReal (min (max (g x) (-(n : ℝ))) (n : ℝ)) ∂(ν : Measure Ω)))
      Filter.atTop
      (nhds (ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω)))) := by
  /- @proof-region region.target-node.session.69fac3f10e8ed3f1 begin -/
  intro Ω _ _ _ _ ν g hg
  have h_eq : ∀ (y : ℝ) (n : ℕ),
      ENNReal.ofReal (min (max y (-(n : ℝ))) (n : ℝ)) = ENNReal.ofReal (min y (n : ℝ)) := by
    intro y n
    by_cases hy : 0 ≤ y
    · have hmax : max y (-(n : ℝ)) = y :=
        max_eq_left (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)
      rw [hmax]
    · have hy' : y ≤ 0 := (not_le.mp hy).le
      have hA : min (max y (-(n : ℝ))) (n : ℝ) ≤ 0 :=
        le_trans (min_le_left _ _) (max_le hy' (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith))
      have hB : min y (n : ℝ) ≤ 0 := le_trans (min_le_left _ _) hy'
      rw [ENNReal.ofReal_eq_zero.mpr hA, ENNReal.ofReal_eq_zero.mpr hB]
  simp only [h_eq]
  let a : ℕ → ENNReal := fun n => ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂(ν : Measure Ω)
  change Filter.Tendsto (fun n => ENNReal.toEReal (a n)) Filter.atTop
    (nhds (ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω))))
  have hmeas : ∀ n : ℕ, Measurable fun x : Ω => ENNReal.ofReal (min (g x) (n : ℝ)) :=
    fun n => (hg.min measurable_const).ennreal_ofReal
  have hmono : Monotone a := by
    intro n m hnm
    refine lintegral_mono (fun x => ENNReal.ofReal_le_ofReal ?_)
    exact min_le_min le_rfl (by exact_mod_cast hnm)
  have hmono2 : Monotone (fun (n : ℕ) (x : Ω) => ENNReal.ofReal (min (g x) (n : ℝ))) := by
    intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hnm))
  have hsup : ∀ x : Ω, (⨆ n : ℕ, ENNReal.ofReal (min (g x) (n : ℝ))) = ENNReal.ofReal (g x) := by
    intro x
    refine le_antisymm (iSup_le (fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _))) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (g x)
    calc ENNReal.ofReal (g x) = ENNReal.ofReal (min (g x) (n : ℝ)) := by rw [min_eq_left hn]
      _ ≤ ⨆ m : ℕ, ENNReal.ofReal (min (g x) (m : ℝ)) :=
        le_iSup (fun m : ℕ => ENNReal.ofReal (min (g x) (m : ℝ))) n
  have hS : (⨆ n, a n) = ∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω) := by
    have h1 : ∫⁻ x, (⨆ n : ℕ, ENNReal.ofReal (min (g x) (n : ℝ))) ∂(ν : Measure Ω) = ⨆ n, a n :=
      lintegral_iSup hmeas hmono2
    rw [← h1]
    simp only [hsup]
  have htoEReal_top : ENNReal.toEReal (⊤ : ENNReal) = (⊤ : EReal) := rfl
  have hcoe : ∀ {c : ENNReal}, c ≠ ⊤ → ENNReal.toEReal c = ((c.toNNReal : ℝ) : EReal) := by
    intro c hc
    conv_lhs => rw [← ENNReal.coe_toNNReal hc]
    rfl
  have hmono_toEReal : Monotone ENNReal.toEReal := by
    intro x y hxy
    rcases eq_or_ne x ⊤ with hx | hx
    · have hy : y = ⊤ := by
        rw [hx] at hxy
        exact le_antisymm le_top hxy
      rw [hx, hy, htoEReal_top]
    · rcases eq_or_ne y ⊤ with hy | hy
      · rw [hy, htoEReal_top]
        exact le_top
      · rw [hcoe hx, hcoe hy]
        have h1 : x.toNNReal ≤ y.toNNReal := by
          have h2 : (↑x.toNNReal : ENNReal) ≤ (↑y.toNNReal : ENNReal) := by
            rw [ENNReal.coe_toNNReal hx, ENNReal.coe_toNNReal hy]
            exact hxy
          exact_mod_cast h2
        exact_mod_cast h1
  have hmonoEReal : Monotone fun n => ENNReal.toEReal (a n) := fun n m hnm =>
    hmono_toEReal (hmono hnm)
  have hdecomp : ∀ x : EReal, x = ⊥ ∨ (∃ r : ℝ, x = ↑r) ∨ x = ⊤ := by
    intro x
    match x with
    | ⊥ => exact Or.inl rfl
    | ⊤ => exact Or.inr (Or.inr rfl)
    | (r : ℝ) => exact Or.inr (Or.inl ⟨r, rfl⟩)
  have hinj : Function.Injective ENNReal.toEReal := by
    intro x y hxy
    rcases eq_or_ne x ⊤ with hx | hx
    · rcases eq_or_ne y ⊤ with hy | hy
      · rw [hx, hy]
      · rw [hx, htoEReal_top, hcoe hy] at hxy
        exact absurd hxy (by simp)
    · rcases eq_or_ne y ⊤ with hy | hy
      · rw [hy, htoEReal_top, hcoe hx] at hxy
        exact absurd hxy (by simp)
      · rw [hcoe hx, hcoe hy] at hxy
        have h2 : (x.toNNReal : ℝ) = (y.toNNReal : ℝ) := by exact_mod_cast hxy
        have h3 : x.toNNReal = y.toNNReal := by exact_mod_cast h2
        rw [← ENNReal.coe_toNNReal hx, ← ENNReal.coe_toNNReal hy, h3]
  have hstrict : StrictMono ENNReal.toEReal := fun x y hxy =>
    lt_of_le_of_ne (hmono_toEReal hxy.le) fun h => absurd (hinj h) hxy.ne
  have hzero : ENNReal.toEReal (0 : ENNReal) = ((0 : ℝ) : EReal) := by
    rw [hcoe (by simp : (0 : ENNReal) ≠ ⊤)]
    simp
  have h0U : ((0 : ℝ) : EReal) ≤ ⨆ n, ENNReal.toEReal (a n) := by
    refine le_trans ?_ (le_iSup (fun n => ENNReal.toEReal (a n)) 0)
    rw [← hzero]
    exact hmono_toEReal (zero_le (a 0))
  have hex : ∀ r : ℝ, ENNReal.ofReal r < ⨆ n, a n → ∃ n : ℕ, ENNReal.ofReal r < a n := by
    intro r hlt
    by_contra hcon
    push_neg at hcon
    exact absurd (iSup_le hcon) (not_le.mpr hlt)
  have hsupEReal : (⨆ n, ENNReal.toEReal (a n))
      = ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure Ω)) := by
    rw [← hS]
    refine le_antisymm (iSup_le fun n => hmono_toEReal (le_iSup a n)) ?_
    refine le_of_forall_lt (fun c hc => ?_)
    rcases hdecomp c with rfl | ⟨r, rfl⟩ | rfl
    · exact lt_of_lt_of_le (by simp) h0U
    · by_cases hr : 0 ≤ r
      · have hof : ENNReal.toEReal (ENNReal.ofReal r) = ((r : ℝ) : EReal) := by
          rw [hcoe ENNReal.ofReal_ne_top, ENNReal.coe_toNNReal_eq_toReal,
            ENNReal.toReal_ofReal_eq_iff.mpr hr]
        have hltS : ENNReal.ofReal r < ⨆ n, a n := by
          by_contra hcon
          rw [not_lt] at hcon
          exact absurd (le_trans (hmono_toEReal hcon) (le_of_eq hof)) (not_le.mpr hc)
        obtain ⟨n, hn⟩ := hex r hltS
        exact lt_of_lt_of_le (by rw [← hof]; exact hstrict hn)
          (le_iSup (fun n => ENNReal.toEReal (a n)) n)
      · exact lt_of_lt_of_le (by exact_mod_cast lt_of_not_ge hr) h0U
    · exact absurd hc (not_lt.mpr le_top)
  have hlim := tendsto_atTop_iSup hmonoEReal
  rwa [hsupEReal] at hlim
  /- @proof-region region.target-node.session.69fac3f10e8ed3f1 end -/

end
end Statlib.Imported
