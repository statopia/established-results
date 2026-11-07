import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Lean
import ProverJobs.job_paper_ed515f3f70ec457d86e430f1b91735bf.Base

namespace PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DCFBlockSwap
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `DCFBlockSwap then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.DCFBlockSwap))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_ed515f3f70ec457d86e430f1b91735bf.Statlib.Imported
noncomputable section
lemma combVec_swap {p : ℕ} (n m : ℕ) (d : ℝ) (muX muY : Fin p → ℝ)
    (X : Fin n → Fin p → ℝ) (Y : Fin m → Fin p → ℝ) :
    combVec m n 1 (fun j => d * muY j) muX (fun i j => d * Y i j) X =
      combVec n m d muX muY X Y := by
  funext j
  simp only [combVec, normSum, ← Finset.mul_sum]
  ring
lemma rho_swap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n m p : ℕ) (d : ℝ) (muX muY : Fin p → ℝ)
    (X F : Fin n → Ω → Fin p → ℝ) (Y G : Fin m → Ω → Fin p → ℝ) :
    rho P m n p 1 (fun j => d * muY j) muX
      (fun i w j => d * Y i w j) X (fun i w j => d * G i w j) F =
      rho P n m p d muX muY X Y F G := by
  unfold rho
  simp_rw [combVec_swap]
lemma LY_swap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (n : ℕ) (muX : Fin p → ℝ) (X : Fin n → Ω → Fin p → ℝ) :
    LY P n muX X = LX P n muX X := rfl
lemma Mstar_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (n : ℕ) (muX : Fin p → ℝ) (X F : Fin n → Ω → Fin p → ℝ) (phi : ℝ) :
    Mstar P n 1 muX X F phi = Mn P n muX X F phi := by
  simp [Mstar, MY, MG, Mn, MX, MF]
open Statlib.StatFoundation.RandomVariable.Gaussian
lemma gaussian_scale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (X : Ω → Fin p → ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (hX : IsCenteredGaussianVector P X S) (d : ℝ) :
    IsCenteredGaussianVector P (fun w j => d * X w j) (fun j k => d ^ 2 * S j k) := by
  have hlin (u : Fin p → ℝ) (w : Ω) :
      (∑ j, u j * (d * X w j)) = ∑ j, (u j * d) * X w j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_pi_lambda _ (fun j => measurable_const.mul
      ((measurable_pi_apply j).comp hX.measurable))
  · intro u
    simpa only [hlin] using hX.integrable_exp (fun j => u j * d)
  · intro u
    simp_rw [hlin]
    rw [hX.mgf_eq]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
lemma covariance_scale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p n : ℕ}
    (mu : Fin p → ℝ) (X : Fin n → Ω → Fin p → ℝ) (d : ℝ) (i : Fin n) :
    covX P (fun j => d * mu j) (fun i w j => d * X i w j) i =
      fun j k => d ^ 2 * covY P mu X i j k := by
  funext j k
  unfold covX covY
  calc
    _ = ∫ w, d ^ 2 * ((X i w j - mu j) * (X i w k - mu k)) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w => by ring)
    _ = _ := integral_const_mul _ _

lemma independent_swap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m p : ℕ}
    (X F : Fin n → Ω → Fin p → ℝ) (Y G : Fin m → Ω → Fin p → ℝ)
    (h : iIndepFun (β := fun _ => Fin p → ℝ) (jointFam X Y F G) P) (d : ℝ) :
    iIndepFun (β := fun _ => Fin p → ℝ)
      (jointFam (fun i w j => d * Y i w j) X (fun i w j => d * G i w j) F) P := by
  let perm : (Fin m ⊕ (Fin n ⊕ (Fin m ⊕ Fin n))) →
      (Fin n ⊕ (Fin m ⊕ (Fin n ⊕ Fin m)))
    | Sum.inl i => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inl i) => Sum.inl i
    | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (Sum.inr (Sum.inr i))
    | Sum.inr (Sum.inr (Sum.inr i)) => Sum.inr (Sum.inr (Sum.inl i))
  let c : (Fin m ⊕ (Fin n ⊕ (Fin m ⊕ Fin n))) → ℝ
    | Sum.inl _ => d
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr (Sum.inl _)) => d
    | Sum.inr (Sum.inr (Sum.inr _)) => 1
  have hinj : Function.Injective perm := by
    intro a b hab
    rcases a with a | a | a | a <;> rcases b with b | b | b | b <;>
      simp_all [perm]
  have h0 := iIndepFun.precomp hinj h
  have h1 := h0.comp (fun i => fun z : Fin p → ℝ => fun j => c i * z j)
    (fun i => measurable_pi_lambda _ (fun j => measurable_const.mul (measurable_pi_apply j)))
  have heq : (fun i w j => c i * jointFam X Y F G (perm i) w j) =
      jointFam (fun i w j => d * Y i w j) X (fun i w j => d * G i w j) F := by
    funext i w j
    rcases i with i | i | i | i <;> simp [c, perm, jointFam]
  change iIndepFun (β := fun _ => Fin p → ℝ)
    (fun i w j => c i * jointFam X Y F G (perm i) w j) P at h1
  rwa [heq] at h1

def row {p : ℕ} (n : ℕ) (d t v : ℝ) (mu A B C : Fin p → ℝ) : Fin p → ℝ :=
  fun j => (Real.sqrt (n : ℝ))⁻¹ * d *
    (Real.sqrt t * (Real.sqrt v * (A j - mu j) + Real.sqrt (1-v) * (B j - mu j)) +
      Real.sqrt (1-t) * (C j - mu j))
def rowDot {p : ℕ} (n : ℕ) (d t v : ℝ) (mu A B C : Fin p → ℝ) : Fin p → ℝ :=
  fun j => (Real.sqrt (n : ℝ))⁻¹ * d *
    ((2 * Real.sqrt t)⁻¹ * (Real.sqrt v * (A j - mu j) + Real.sqrt (1-v) * (B j - mu j)) -
      (2 * Real.sqrt (1-t))⁻¹ * (C j - mu j))
lemma row_scale {p : ℕ} (n : ℕ) (d t v : ℝ) (mu A B C : Fin p → ℝ) :
    row n 1 t v (fun j => d*mu j) (fun j => d*A j) (fun j => d*B j) (fun j => d*C j) =
      row n d t v mu A B C := by
  funext j
  simp only [row]
  ring
lemma rowDot_scale {p : ℕ} (n : ℕ) (d t v : ℝ) (mu A B C : Fin p → ℝ) :
    rowDot n 1 t v (fun j => d*mu j) (fun j => d*A j) (fun j => d*B j) (fun j => d*C j) =
      rowDot n d t v mu A B C := by
  funext j
  simp only [rowDot]
  ring
lemma interpolant_swap {p : ℕ} (n m : ℕ) (d t v : ℝ) (muX muY : Fin p → ℝ)
    (X F F' : Fin n → Fin p → ℝ) (Y G G' : Fin m → Fin p → ℝ) :
    (fun j =>
      (∑ i, row m 1 t v (fun j => d*muY j) (fun j => d*Y i j)
        (fun j => d*G i j) (fun j => d*G' i j) j) +
      (∑ i, row n 1 t v muX (X i) (F i) (F' i) j)) =
    (fun j => (∑ i, row n 1 t v muX (X i) (F i) (F' i) j) +
      (∑ i, row m d t v muY (Y i) (G i) (G' i) j)) := by
  simp_rw [row_scale]
  funext j
  exact add_comm _ _

end
end DCFBlockSwap




