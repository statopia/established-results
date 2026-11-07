import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Vocabulary
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.ProvedNodes.Node_1913777471_3deb48ab_61cafb65

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Statlib.StatFoundation.RandomVariable.Gaussian
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4050339779_734b360b : ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n m p : ℕ) (delta : ℕ → ℕ → ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (Y : Fin m → Ω → Fin p → ℝ)
    (F : Fin n → Ω → Fin p → ℝ) (G : Fin m → Ω → Fin p → ℝ)
    (hn : 0 < n) (hm : 0 < m) (hp : 0 < p)
    (hXm : ∀ i : Fin n, Measurable (X i))
    (hYm : ∀ i : Fin m, Measurable (Y i))
    (hFm : ∀ i : Fin n, Measurable (F i))
    (hGm : ∀ i : Fin m, Measurable (G i))
    (hindep : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P)
    (hXmean : ∀ (i : Fin n) (j : Fin p), ∫ ω, X i ω j ∂P = muX j)
    (hYmean : ∀ (i : Fin m) (j : Fin p), ∫ ω, Y i ω j ∂P = muY j)
    (hXL2 : ∀ (i : Fin n) (j : Fin p), MemLp (fun ω => X i ω j) 2 P)
    (hYL2 : ∀ (i : Fin m) (j : Fin p), MemLp (fun ω => Y i ω j) 2 P)
    (hX3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |X i ω j - muX j| ^ 3) P)
    (hY3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |Y i ω j - muY j| ^ 3) P)
    (hF3 : ∀ (i : Fin n) (j : Fin p), Integrable (fun ω => |F i ω j - muX j| ^ 3) P)
    (hG3 : ∀ (i : Fin m) (j : Fin p), Integrable (fun ω => |G i ω j - muY j| ^ 3) P)
    (hFcov : ∀ i : Fin n,
      IsCenteredGaussianVector P (fun ω j => F i ω j - muX j) (covX P muX X i))
    (hGcov : ∀ i : Fin m,
      IsCenteredGaussianVector P (fun ω j => G i ω j - muY j) (covY P muY Y i))
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1),
    ∀ t : ℝ, 0 < t → t < 1 → ∀ (i : Fin n) (j k : Fin p),
      let Zs : Ω × Ω → ℝ := fun x =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt t *
              (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k))
            + Real.sqrt (1 - t) * (F i x.2 k - muX k))
      let Zd : Ω × Ω → ℝ := fun x =>
        (Real.sqrt (n : ℝ))⁻¹ *
          ((2 * Real.sqrt t)⁻¹ *
              (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))
            - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j))
      Integrable (fun x => Zs x * Zd x) (P.prod P) ∧
        ∫ x, Zs x * Zd x ∂(P.prod P) = 0 := by
  /- @proof-region region.target-node.session.fe6bf6299ec6d64f begin -/
  intro Ω instΩ P instP n m p delta muX muY X Y F G hn hm hp hXm hYm hFm hGm hindep
    hXmean hYmean hXL2 hYL2 hX3 hY3 hF3 hG3 hFcov hGcov v hv0 hv1 t ht0 ht1 i j k
  dsimp only
  have hmom := statopia_math_node_1913777471_3deb48ab P muX X i (fun (j : Fin p) => hXL2 i j) (fun (ω : Ω) (j : Fin p) => F i ω j - muX j) (hFcov i)
  have hBmean : ∀ m : Fin p, ∫ ω, (F i ω m - muX m) ∂P = 0 := hmom.1
  have hBcov : ∀ m l : Fin p, ∫ ω, (F i ω m - muX m) * (F i ω l - muX l) ∂P = covX P muX X i m l := hmom.2
  have hAmean : ∀ m : Fin p, ∫ ω, (X i ω m - muX m) ∂P = 0 := by
    intro m
    have hiX : Integrable (fun ω => X i ω m) P := (hXL2 i m).integrable (by norm_num)
    rw [integral_sub hiX (integrable_const (muX m)), hXmean i m]
    simp [integral_const]
  have hAcov : ∀ m l : Fin p, ∫ ω, (X i ω m - muX m) * (X i ω l - muX l) ∂P = covX P muX X i m l := by
    intro m l
    rfl
  have hA2 : ∀ m : Fin p, MemLp (fun ω => X i ω m - muX m) 2 P := by
    intro m
    exact (hXL2 i m).sub (memLp_const (muX m))
  have hbnd : ∀ x : ℝ, |x| ^ 2 ≤ |x| ^ 3 + 1 := by
    intro x
    have hy : (0:ℝ) ≤ |x| := abs_nonneg x
    by_cases h : |x| ≤ 1
    · have h1 : |x| ^ 2 ≤ 1 := by nlinarith
      have h3 : (0:ℝ) ≤ |x| ^ 3 := pow_nonneg hy 3
      linarith
    · push_neg at h
      have h1 : |x| ^ 2 ≤ |x| ^ 3 := by
        have hm := mul_le_mul_of_nonneg_left h.le (sq_nonneg |x|)
        nlinarith [hm]
      linarith
  have hB2 : ∀ m : Fin p, MemLp (fun ω => F i ω m - muX m) 2 P := by
    intro m
    rw [memLp_two_iff_integrable_sq]
    have hmeas : AEStronglyMeasurable (fun ω => (F i ω m - muX m) ^ 2) P := by measurability
    have hgint : Integrable (fun ω => |F i ω m - muX m| ^ 3 + 1) P :=
      Integrable.add (hF3 i m) (integrable_const 1)
    refine Integrable.mono hgint hmeas ?_
    filter_upwards with ω
    have hgf : ‖(fun ω => |F i ω m - muX m| ^ 3 + 1) ω‖ = |F i ω m - muX m| ^ 3 + 1 := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    rw [hgf, ← sq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbnd (F i ω m - muX m)
    measurability
  refine ⟨?_, ?_⟩
  · have hAk : Integrable (fun ω => X i ω k - muX k) P := MeasureTheory.MemLp.integrable (by norm_num) (hA2 k)
    have hBk : Integrable (fun ω => F i ω k - muX k) P := MeasureTheory.MemLp.integrable (by norm_num) (hB2 k)
    have hAj : Integrable (fun ω => X i ω j - muX j) P := MeasureTheory.MemLp.integrable (by norm_num) (hA2 j)
    have hBj : Integrable (fun ω => F i ω j - muX j) P := MeasureTheory.MemLp.integrable (by norm_num) (hB2 j)
    have hAA : Integrable (fun ω => (X i ω k - muX k) * (X i ω j - muX j)) P := MemLp.integrable_mul (hA2 k) (hA2 j)
    have hAB : Integrable (fun ω => (X i ω k - muX k) * (F i ω j - muX j)) P := MemLp.integrable_mul (hA2 k) (hB2 j)
    have hBA : Integrable (fun ω => (F i ω k - muX k) * (X i ω j - muX j)) P := MemLp.integrable_mul (hB2 k) (hA2 j)
    have hBB : Integrable (fun ω => (F i ω k - muX k) * (F i ω j - muX j)) P := MemLp.integrable_mul (hB2 k) (hB2 j)
    have hPk : Integrable (fun ω => Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) P :=
      Integrable.add (hAk.const_mul (Real.sqrt v)) (hBk.const_mul (Real.sqrt (1 - v)))
    have hPj : Integrable (fun ω => Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j)) P :=
      Integrable.add (hAj.const_mul (Real.sqrt v)) (hBj.const_mul (Real.sqrt (1 - v)))
    have hPkPj : Integrable (fun ω => (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j))) P := by
      rw [show (fun ω => (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j))) = fun ω => (Real.sqrt v * Real.sqrt v) * ((X i ω k - muX k) * (X i ω j - muX j)) + (Real.sqrt v * Real.sqrt (1 - v)) * ((X i ω k - muX k) * (F i ω j - muX j)) + (Real.sqrt (1 - v) * Real.sqrt v) * ((F i ω k - muX k) * (X i ω j - muX j)) + (Real.sqrt (1 - v) * Real.sqrt (1 - v)) * ((F i ω k - muX k) * (F i ω j - muX j)) from by funext ω; ring]
      exact Integrable.add (Integrable.add (Integrable.add (hAA.const_mul _) (hAB.const_mul _)) (hBA.const_mul _)) (hBB.const_mul _)
    have iT1 : Integrable (fun x : Ω × Ω => (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹) * ((Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)))) (P.prod P) := by
      have h := Integrable.mul_prod (hPkPj.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹))) (integrable_const (1:ℝ) : Integrable (fun _ : Ω => (1:ℝ)) P)
      simpa only [mul_one] using h
    have iT2 : Integrable (fun x : Ω × Ω => (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹)) * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (F i x.2 j - muX j)) (P.prod P) := by
      have h := Integrable.mul_prod (hPk.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹)))) hBj
      simpa only using h
    have iT3 : Integrable (fun x : Ω × Ω => (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) * (F i x.2 k - muX k)) (P.prod P) := by
      have h := Integrable.mul_prod (hPj.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹))) hBk
      simpa only using h
    have iT4 : Integrable (fun x : Ω × Ω => (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹)) * ((F i x.2 k - muX k) * (F i x.2 j - muX j))) (P.prod P) := by
      have h := Integrable.mul_prod (integrable_const (1:ℝ) : Integrable (fun _ : Ω => (1:ℝ)) P) (hBB.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))))
      simpa only [one_mul] using h
    rw [show (fun x : Ω × Ω => (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) + Real.sqrt (1 - t) * (F i x.2 k - muX k)) * ((Real.sqrt (n:ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)))) = fun x => (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹) * ((Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) + (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹)) * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (F i x.2 j - muX j) + (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) * (F i x.2 k - muX k) + (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹)) * ((F i x.2 k - muX k) * (F i x.2 j - muX j)) from by funext x; ring]
    exact Integrable.add (Integrable.add (Integrable.add iT1 iT2) iT3) iT4
  · have hXF : (fun ω => X i ω) ⟂ᵢ[P] (fun ω => F i ω) :=
      iIndepFun.indepFun hindep (i := Sum.inl i) (j := Sum.inr (Sum.inr (Sum.inl i))) (by simp)
    have hmk : Measurable (fun v : Fin p → ℝ => v k - muX k) := ((continuous_apply k).sub continuous_const).measurable
    have hmj : Measurable (fun v : Fin p → ℝ => v j - muX j) := ((continuous_apply j).sub continuous_const).measurable
    have hcross1 : ∫ ω, (X i ω k - muX k) * (F i ω j - muX j) ∂P = 0 := by
      have hmain := IndepFun.integral_fun_comp_mul_comp
        (X := fun ω => X i ω) (Y := fun ω => F i ω)
        (f := fun v : Fin p → ℝ => v k - muX k) (g := fun v : Fin p → ℝ => v j - muX j)
        hXF (hXm i).aemeasurable (hFm i).aemeasurable hmk.aestronglyMeasurable hmj.aestronglyMeasurable
      show ∫ ω, (fun v : Fin p → ℝ => v k - muX k) (X i ω) * (fun v : Fin p → ℝ => v j - muX j) (F i ω) ∂P = 0
      rw [hmain]
      simp only [hAmean k, hBmean j, zero_mul]
    have hcross2 : ∫ ω, (F i ω k - muX k) * (X i ω j - muX j) ∂P = 0 := by
      have hmain := IndepFun.integral_fun_comp_mul_comp
        (X := fun ω => F i ω) (Y := fun ω => X i ω)
        (f := fun v : Fin p → ℝ => v k - muX k) (g := fun v : Fin p → ℝ => v j - muX j)
        hXF.symm (hFm i).aemeasurable (hXm i).aemeasurable hmk.aestronglyMeasurable hmj.aestronglyMeasurable
      show ∫ ω, (fun v : Fin p → ℝ => v k - muX k) (F i ω) * (fun v : Fin p → ℝ => v j - muX j) (X i ω) ∂P = 0
      rw [hmain]
      simp only [hBmean k, zero_mul]
    have hAA2 : Integrable (fun ω => (X i ω k - muX k) * (X i ω j - muX j)) P := MemLp.integrable_mul (hA2 k) (hA2 j)
    have hAB2 : Integrable (fun ω => (X i ω k - muX k) * (F i ω j - muX j)) P := MemLp.integrable_mul (hA2 k) (hB2 j)
    have hBA2 : Integrable (fun ω => (F i ω k - muX k) * (X i ω j - muX j)) P := MemLp.integrable_mul (hB2 k) (hA2 j)
    have hBB2 : Integrable (fun ω => (F i ω k - muX k) * (F i ω j - muX j)) P := MemLp.integrable_mul (hB2 k) (hB2 j)
    have hPkPjval : ∫ ω, (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j)) ∂P = covX P muX X i k j := by
      rw [show (fun ω => (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j))) = fun ω => (Real.sqrt v * Real.sqrt v) * ((X i ω k - muX k) * (X i ω j - muX j)) + (Real.sqrt v * Real.sqrt (1 - v)) * ((X i ω k - muX k) * (F i ω j - muX j)) + (Real.sqrt (1 - v) * Real.sqrt v) * ((F i ω k - muX k) * (X i ω j - muX j)) + (Real.sqrt (1 - v) * Real.sqrt (1 - v)) * ((F i ω k - muX k) * (F i ω j - muX j)) from by funext ω; ring]
      have i1 : Integrable (fun ω => (Real.sqrt v * Real.sqrt v) * ((X i ω k - muX k) * (X i ω j - muX j))) P := hAA2.const_mul (Real.sqrt v * Real.sqrt v)
      have i2 : Integrable (fun ω => (Real.sqrt v * Real.sqrt (1 - v)) * ((X i ω k - muX k) * (F i ω j - muX j))) P := hAB2.const_mul (Real.sqrt v * Real.sqrt (1 - v))
      have i3 : Integrable (fun ω => (Real.sqrt (1 - v) * Real.sqrt v) * ((F i ω k - muX k) * (X i ω j - muX j))) P := hBA2.const_mul (Real.sqrt (1 - v) * Real.sqrt v)
      have i4 : Integrable (fun ω => (Real.sqrt (1 - v) * Real.sqrt (1 - v)) * ((F i ω k - muX k) * (F i ω j - muX j))) P := hBB2.const_mul (Real.sqrt (1 - v) * Real.sqrt (1 - v))
      have x1 := integral_add (Integrable.add (Integrable.add i1 i2) i3) i4
      have x2 := integral_add (Integrable.add i1 i2) i3
      have x3 := integral_add i1 i2
      simp only [Pi.add_apply] at x1 x2 x3 ⊢
      rw [x1, x2, x3]
      simp only [integral_const_mul]
      rw [hAcov k j, hcross1, hcross2, hBcov k j]
      rw [Real.mul_self_sqrt hv0, Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ 1 - v)]
      ring
    have hAk : Integrable (fun ω => X i ω k - muX k) P := MeasureTheory.MemLp.integrable (by norm_num) (hA2 k)
    have hBk : Integrable (fun ω => F i ω k - muX k) P := MeasureTheory.MemLp.integrable (by norm_num) (hB2 k)
    have hAj : Integrable (fun ω => X i ω j - muX j) P := MeasureTheory.MemLp.integrable (by norm_num) (hA2 j)
    have hBj : Integrable (fun ω => F i ω j - muX j) P := MeasureTheory.MemLp.integrable (by norm_num) (hB2 j)
    have hPk : Integrable (fun ω => Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) P := Integrable.add (hAk.const_mul (Real.sqrt v)) (hBk.const_mul (Real.sqrt (1 - v)))
    have hPj : Integrable (fun ω => Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j)) P := Integrable.add (hAj.const_mul (Real.sqrt v)) (hBj.const_mul (Real.sqrt (1 - v)))
    have hPkPjI : Integrable (fun ω => (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j))) P := by
      rw [show (fun ω => (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j))) = fun ω => (Real.sqrt v * Real.sqrt v) * ((X i ω k - muX k) * (X i ω j - muX j)) + (Real.sqrt v * Real.sqrt (1 - v)) * ((X i ω k - muX k) * (F i ω j - muX j)) + (Real.sqrt (1 - v) * Real.sqrt v) * ((F i ω k - muX k) * (X i ω j - muX j)) + (Real.sqrt (1 - v) * Real.sqrt (1 - v)) * ((F i ω k - muX k) * (F i ω j - muX j)) from by funext ω; ring]
      exact Integrable.add (Integrable.add (Integrable.add (hAA2.const_mul _) (hAB2.const_mul _)) (hBA2.const_mul _)) (hBB2.const_mul _)
    have iT1 : Integrable (fun x : Ω × Ω => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹)) * ((Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) * 1) (P.prod P) := by
      have h := Integrable.mul_prod (hPkPjI.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹))) (integrable_const (1:ℝ) : Integrable (fun _ : Ω => (1:ℝ)) P)
      exact h
    have iT2 : Integrable (fun x : Ω × Ω => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹))) * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (F i x.2 j - muX j)) (P.prod P) := by
      have h := Integrable.mul_prod (hPk.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹)))) hBj
      exact h
    have iT3 : Integrable (fun x : Ω × Ω => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) * (F i x.2 k - muX k)) (P.prod P) := by
      have h := Integrable.mul_prod (hPj.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹))) hBk
      exact h
    have iT4 : Integrable (fun x : Ω × Ω => (1:ℝ) * (((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))) * ((F i x.2 k - muX k) * (F i x.2 j - muX j)))) (P.prod P) := by
      have h := Integrable.mul_prod (integrable_const (1:ℝ) : Integrable (fun _ : Ω => (1:ℝ)) P) (hBB2.const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))))
      exact h
    rw [show (fun x : Ω × Ω => (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) + Real.sqrt (1 - t) * (F i x.2 k - muX k)) * ((Real.sqrt (n:ℝ))⁻¹ * ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) - (2 * Real.sqrt (1 - t))⁻¹ * (F i x.2 j - muX j)))) = fun x => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹)) * ((Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) * 1 + ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹))) * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (F i x.2 j - muX j) + ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) * (F i x.2 k - muX k) + (1:ℝ) * (((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))) * ((F i x.2 k - muX k) * (F i x.2 j - muX j))) from by funext x; ring]
    have x1 := integral_add (Integrable.add (Integrable.add iT1 iT2) iT3) iT4
    have x2 := integral_add (Integrable.add iT1 iT2) iT3
    have x3 := integral_add iT1 iT2
    simp only [Pi.add_apply] at x1 x2 x3 ⊢
    rw [x1, x2, x3]
    have hs1 : Real.sqrt t * (2 * Real.sqrt t)⁻¹ = 1 / 2 := by
      have h : (Real.sqrt t) ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
      field_simp
    have hs2 : Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹) = -1 / 2 := by
      have h : (Real.sqrt (1 - t)) ≠ 0 := (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - t)).ne'
      field_simp
    have p1 : (∫ x : Ω × Ω, ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹)) * ((Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j))) * 1 ∂(P.prod P)) = ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹)) * covX P muX X i k j := by
      have h := integral_prod_mul (μ := P) (ν := P) (fun ω => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹)) * ((Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j)))) (fun _ : Ω => (1:ℝ))
      rw [h]
      rw [integral_const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (2 * Real.sqrt t)⁻¹)) (fun ω => (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j)))]
      rw [hPkPjval]
      rw [show (∫ y : Ω, (1:ℝ) ∂P) = 1 from by simp]
      ring
    have p2 : (∫ x : Ω × Ω, ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹))) * (Real.sqrt v * (X i x.1 k - muX k) + Real.sqrt (1 - v) * (F i x.1 k - muX k)) * (F i x.2 j - muX j) ∂(P.prod P)) = 0 := by
      have h := integral_prod_mul (μ := P) (ν := P) (fun ω => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt t * (-(2 * Real.sqrt (1 - t))⁻¹))) * (Real.sqrt v * (X i ω k - muX k) + Real.sqrt (1 - v) * (F i ω k - muX k))) (fun ω => F i ω j - muX j)
      rw [h]
      rw [hBmean j]
      ring
    have p3 : (∫ x : Ω × Ω, ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹)) * (Real.sqrt v * (X i x.1 j - muX j) + Real.sqrt (1 - v) * (F i x.1 j - muX j)) * (F i x.2 k - muX k) ∂(P.prod P)) = 0 := by
      have h := integral_prod_mul (μ := P) (ν := P) (fun ω => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (2 * Real.sqrt t)⁻¹)) * (Real.sqrt v * (X i ω j - muX j) + Real.sqrt (1 - v) * (F i ω j - muX j))) (fun ω => F i ω k - muX k)
      rw [h]
      rw [hBmean k]
      ring
    have p4 : (∫ x : Ω × Ω, (1:ℝ) * (((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))) * ((F i x.2 k - muX k) * (F i x.2 j - muX j))) ∂(P.prod P)) = ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))) * covX P muX X i k j := by
      have h := integral_prod_mul (μ := P) (ν := P) (fun _ : Ω => (1:ℝ)) (fun ω => ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))) * ((F i ω k - muX k) * (F i ω j - muX j)))
      rw [h]
      rw [show (∫ y : Ω, (1:ℝ) ∂P) = 1 from by simp]
      rw [integral_const_mul ((Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (n:ℝ))⁻¹ * (Real.sqrt (1 - t) * (-(2 * Real.sqrt (1 - t))⁻¹))) (fun ω => (F i ω k - muX k) * (F i ω j - muX j))]
      rw [hBcov k j]
      ring
    rw [p1, p2, p3, p4, hs1, hs2]
    ring
  /- @proof-region region.target-node.session.fe6bf6299ec6d64f end -/

end

end Statlib.Imported

