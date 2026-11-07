import Lean
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Vocabulary
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Base
import ProverJobs.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.ProvedNodes.Node_283558168_72fffefb_dab35fce

namespace PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5

open scoped BigOperators
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.job_paper_370f7a68a9a1447a9d903f9a55f08bd5.Statlib.Imported

noncomputable section
open scoped BigOperators
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_4085384541_bfcefbca : ∀ (p : ℕ) (hp : 0 < p)
    (beta : ℝ) (hbeta : 0 < beta)
    (phi : ℝ) (hphi : 0 < phi)
    (y : Fin p → ℝ)
    (d1 d2 d3 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3),
    let Z : (Fin p → ℝ) → ℝ :=
      (fun w => ∑ m : Fin p, Real.exp (beta * (w m - y m)));
    let pi : (Fin p → ℝ) → Fin p → ℝ :=
      (fun w j => Real.exp (beta * (w j - y j)) / Z w);
    let W : (Fin p → ℝ) → Fin p → Fin p → ℝ :=
      (fun w j k => pi w j * (if j = k then (1 : ℝ) else 0) + pi w j * pi w k);
    let P : (Fin p → ℝ) → Fin p → Fin p → Fin p → ℝ :=
      (fun w j k l =>
        pi w j * (if j = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
        + pi w j * pi w l * (if j = k then (1 : ℝ) else 0)
        + pi w j * pi w k * (if j = l then (1 : ℝ) else 0)
        + pi w j * pi w k * (if k = l then (1 : ℝ) else 0)
        + 2 * pi w j * pi w k * pi w l);
    let Q : (Fin p → ℝ) → Fin p → Fin p → Fin p → ℝ :=
      (fun w j k l =>
        phi ^ 3 * d3 * pi w j * pi w k * pi w l
        + phi ^ 2 * d2 * beta *
            (W w j k * pi w l + W w j l * pi w k + W w k l * pi w j)
        + phi * d1 * beta ^ 2 * P w j k l);
    ∀ (j k l : Fin p) (w w' : Fin p → ℝ),
      (∀ r : Fin p, |w' r| * beta ≤ 1) →
        (Q w j k l ≤ Real.exp 6 * Q (w + w') j k l ∧
          Q (w + w') j k l ≤ Real.exp 6 * Q w j k l) := by
  /- @proof-region region.target-node.session.38669bc3a29403af begin -/
  intro p hp beta hbeta phi hphi y d1 d2 d3 hd1 hd2 hd3
  let Z : (Fin p → ℝ) → ℝ := fun w => ∑ m : Fin p, Real.exp (beta * (w m - y m))
  let pi : (Fin p → ℝ) → Fin p → ℝ := fun w j => Real.exp (beta * (w j - y j)) / Z w
  let W : (Fin p → ℝ) → Fin p → Fin p → ℝ :=
    fun w j k => pi w j * (if j = k then (1 : ℝ) else 0) + pi w j * pi w k
  let P : (Fin p → ℝ) → Fin p → Fin p → Fin p → ℝ :=
    fun w j k l =>
      pi w j * (if j = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)
      + pi w j * pi w l * (if j = k then (1 : ℝ) else 0)
      + pi w j * pi w k * (if j = l then (1 : ℝ) else 0)
      + pi w j * pi w k * (if k = l then (1 : ℝ) else 0)
      + 2 * pi w j * pi w k * pi w l
  let Q : (Fin p → ℝ) → Fin p → Fin p → Fin p → ℝ :=
    fun w j k l =>
      phi ^ 3 * d3 * pi w j * pi w k * pi w l
      + phi ^ 2 * d2 * beta * (W w j k * pi w l + W w j l * pi w k + W w k l * pi w j)
      + phi * d1 * beta ^ 2 * P w j k l
  show ∀ (j k l : Fin p) (w w' : Fin p → ℝ),
      (∀ r : Fin p, |w' r| * beta ≤ 1) →
        (Q w j k l ≤ Real.exp 6 * Q (w + w') j k l ∧
          Q (w + w') j k l ≤ Real.exp 6 * Q w j k l)
  intro j k l w w' hw'
  have hmain := (statopia_math_node_283558168_72fffefb p hp beta hbeta y).2
  have hZpos : ∀ v : Fin p → ℝ, 0 < Z v := by
    intro v
    have h := (hmain v).1
    dsimp only [Z]
    exact h
  have hpipos : ∀ (v : Fin p → ℝ) (i : Fin p), 0 < pi v i := by
    intro v i
    have h := (hmain v).2.1 i
    dsimp only [pi, Z]
    exact h
  have hx_abs : ∀ x : Fin p, |beta * w' x| ≤ 1 := by
    intro x
    calc |beta * w' x| = |beta| * |w' x| := abs_mul _ _
      _ = beta * |w' x| := by rw [abs_of_pos hbeta]
      _ = |w' x| * beta := by ring
      _ ≤ 1 := hw' x
  have hexpb_ge : ∀ x : Fin p, Real.exp (-1) ≤ Real.exp (beta * w' x) := by
    intro x
    exact Real.exp_le_exp.mpr (abs_le.mp (hx_abs x)).1
  have hexpb_le : ∀ x : Fin p, Real.exp (beta * w' x) ≤ Real.exp 1 := by
    intro x
    exact Real.exp_le_exp.mpr (abs_le.mp (hx_abs x)).2
  have hZ_w' : Z (w + w') = ∑ m : Fin p, Real.exp (beta * (w m - y m)) * Real.exp (beta * w' m) := by
    dsimp only [Z]
    apply Finset.sum_congr rfl
    intro m _
    have harg : beta * ((w + w') m - y m) = beta * (w m - y m) + beta * w' m := by
      simp only [Pi.add_apply]; ring
    rw [harg, Real.exp_add]
  have hZ_le : Z (w + w') ≤ Real.exp 1 * Z w := by
    rw [hZ_w']
    calc ∑ m : Fin p, Real.exp (beta * (w m - y m)) * Real.exp (beta * w' m)
        ≤ ∑ m : Fin p, Real.exp (beta * (w m - y m)) * Real.exp 1 := by
          apply Finset.sum_le_sum
          intro m _
          exact mul_le_mul_of_nonneg_left (hexpb_le m) (Real.exp_pos _).le
      _ = Real.exp 1 * Z w := by
          rw [← Finset.sum_mul]
          dsimp only [Z]
          ring
  have hZ_ge : Real.exp (-1) * Z w ≤ Z (w + w') := by
    rw [hZ_w']
    dsimp only [Z]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    calc Real.exp (-1) * Real.exp (beta * (w m - y m))
        ≤ Real.exp (beta * w' m) * Real.exp (beta * (w m - y m)) :=
          mul_le_mul_of_nonneg_right (hexpb_ge m) (Real.exp_pos _).le
      _ = Real.exp (beta * (w m - y m)) * Real.exp (beta * w' m) := by ring
  have hZw_le : Z w ≤ Real.exp 1 * Z (w + w') := by
    have h := mul_le_mul_of_nonneg_left hZ_ge (Real.exp_pos (1:ℝ)).le
    have he : Real.exp 1 * Real.exp (-1) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hEq : Real.exp 1 * (Real.exp (-1) * Z w) = Z w := by
      rw [← mul_assoc, he, one_mul]
    rwa [hEq] at h
  have hExp1 : ∀ x : Fin p, Real.exp 1 ≤ Real.exp 2 * Real.exp (beta * w' x) := by
    intro x
    have h := mul_le_mul_of_nonneg_left (hexpb_ge x) (Real.exp_pos (2:ℝ)).le
    have he : Real.exp 2 * Real.exp (-1) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rwa [he] at h
  have hkey1 : ∀ x : Fin p, Z (w + w') ≤ Real.exp 2 * Real.exp (beta * w' x) * Z w := by
    intro x
    calc Z (w + w') ≤ Real.exp 1 * Z w := hZ_le
      _ ≤ (Real.exp 2 * Real.exp (beta * w' x)) * Z w :=
          mul_le_mul_of_nonneg_right (hExp1 x) (hZpos w).le
      _ = Real.exp 2 * Real.exp (beta * w' x) * Z w := by ring
  have hkey2 : ∀ x : Fin p, Real.exp (beta * w' x) * Z w ≤ Real.exp 2 * Z (w + w') := by
    intro x
    calc Real.exp (beta * w' x) * Z w ≤ Real.exp 1 * Z w :=
          mul_le_mul_of_nonneg_right (hexpb_le x) (hZpos w).le
      _ ≤ Real.exp 1 * (Real.exp 1 * Z (w + w')) :=
          mul_le_mul_of_nonneg_left hZw_le (Real.exp_pos (1:ℝ)).le
      _ = Real.exp 2 * Z (w + w') := by
          rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num, mul_assoc]
  have hratio_fwd : ∀ x : Fin p, pi (w + w') x ≤ Real.exp 2 * pi w x := by
    intro x
    have hZ'ne : Z (w + w') ≠ 0 := ne_of_gt (hZpos (w + w'))
    have hZwne : Z w ≠ 0 := ne_of_gt (hZpos w)
    have hnum : Real.exp (beta * ((w + w') x - y x)) =
        Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x) := by
      rw [show beta * ((w + w') x - y x) = beta * (w x - y x) + beta * w' x by
        simp only [Pi.add_apply]; ring]
      rw [Real.exp_add]
    have hmain' : (Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x)) * Z w
        ≤ (Real.exp 2 * Real.exp (beta * (w x - y x))) * Z (w + w') := by
      calc (Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x)) * Z w
          = Real.exp (beta * (w x - y x)) * (Real.exp (beta * w' x) * Z w) := by ring
        _ ≤ Real.exp (beta * (w x - y x)) * (Real.exp 2 * Z (w + w')) :=
            mul_le_mul_of_nonneg_left (hkey2 x) (Real.exp_pos _).le
        _ = (Real.exp 2 * Real.exp (beta * (w x - y x))) * Z (w + w') := by ring
    dsimp only [pi]
    rw [hnum]
    rw [div_le_iff₀ (hZpos (w + w'))]
    rw [show (Real.exp 2 * (Real.exp (beta * (w x - y x)) / Z w)) * Z (w + w')
        = Real.exp 2 * Real.exp (beta * (w x - y x)) * Z (w + w') / Z w by ring_nf]
    rw [le_div_iff₀ (hZpos w)]
    linarith [hmain']
  have hratio_bwd : ∀ x : Fin p, pi w x ≤ Real.exp 2 * pi (w + w') x := by
    intro x
    have hZ'ne : Z (w + w') ≠ 0 := ne_of_gt (hZpos (w + w'))
    have hZwne : Z w ≠ 0 := ne_of_gt (hZpos w)
    have hnum : Real.exp (beta * ((w + w') x - y x)) =
        Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x) := by
      rw [show beta * ((w + w') x - y x) = beta * (w x - y x) + beta * w' x by
        simp only [Pi.add_apply]; ring]
      rw [Real.exp_add]
    have hkey : Real.exp (beta * (w x - y x)) * Z (w + w')
        ≤ Real.exp 2 * (Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x)) * Z w := by
      calc Real.exp (beta * (w x - y x)) * Z (w + w')
          ≤ Real.exp (beta * (w x - y x)) * (Real.exp 2 * Real.exp (beta * w' x) * Z w) :=
            mul_le_mul_of_nonneg_left (hkey1 x) (Real.exp_pos _).le
        _ = Real.exp 2 * (Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x)) * Z w := by ring
    dsimp only [pi]
    rw [hnum]
    rw [div_le_iff₀ (hZpos w)]
    rw [show (Real.exp 2 * (Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x) / Z (w + w'))) * Z w
        = Real.exp 2 * (Real.exp (beta * (w x - y x)) * Real.exp (beta * w' x)) * Z w / Z (w + w') by ring_nf]
    rw [le_div_iff₀ (hZpos (w + w'))]
    linarith [hkey]
  have hexp4_le_6 : Real.exp 4 ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
  have hexp2_le_6 : Real.exp 2 ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
  have monomial1 : ∀ a a' : ℝ, 0 ≤ a' → a ≤ Real.exp 2 * a' → a ≤ Real.exp 6 * a' := by
    intro a a' ha' ha
    calc a ≤ Real.exp 2 * a' := ha
      _ ≤ Real.exp 6 * a' := mul_le_mul_of_nonneg_right hexp2_le_6 ha'
  have monomial2 : ∀ a c a' c' : ℝ, 0 ≤ c → 0 ≤ a' → 0 ≤ c' →
      a ≤ Real.exp 2 * a' → c ≤ Real.exp 2 * c' → a * c ≤ Real.exp 6 * (a' * c') := by
    intro a c a' c' hc ha' hc' ha hcc
    have h1 : a * c ≤ (Real.exp 2 * a') * (Real.exp 2 * c') :=
      mul_le_mul ha hcc hc (mul_nonneg (Real.exp_pos 2).le ha')
    have h2 : (Real.exp 2 * a') * (Real.exp 2 * c') = Real.exp 4 * (a' * c') := by
      rw [show Real.exp 4 = Real.exp 2 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
      ring
    rw [h2] at h1
    calc a * c ≤ Real.exp 4 * (a' * c') := h1
      _ ≤ Real.exp 6 * (a' * c') := mul_le_mul_of_nonneg_right hexp4_le_6 (mul_nonneg ha' hc')
  have monomial3 : ∀ a b c a' b' c' : ℝ, 0 ≤ b → 0 ≤ c → 0 ≤ a' → 0 ≤ b' → 0 ≤ c' →
      a ≤ Real.exp 2 * a' → b ≤ Real.exp 2 * b' → c ≤ Real.exp 2 * c' →
      a * b * c ≤ Real.exp 6 * (a' * b' * c') := by
    intro a b c a' b' c' hb hc ha' hb' hc' ha hb2 hc2
    have h1 : a * b ≤ (Real.exp 2 * a') * (Real.exp 2 * b') :=
      mul_le_mul ha hb2 hb (mul_nonneg (Real.exp_pos 2).le ha')
    have h1' : a * b ≤ Real.exp 4 * (a' * b') := by
      have h2 : (Real.exp 2 * a') * (Real.exp 2 * b') = Real.exp 4 * (a' * b') := by
        rw [show Real.exp 4 = Real.exp 2 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
        ring
      rwa [h2] at h1
    have h3 : a * b * c ≤ (Real.exp 4 * (a' * b')) * (Real.exp 2 * c') :=
      mul_le_mul h1' hc2 hc (mul_nonneg (Real.exp_pos 4).le (mul_nonneg ha' hb'))
    have h4 : (Real.exp 4 * (a' * b')) * (Real.exp 2 * c') = Real.exp 6 * (a' * b' * c') := by
      rw [show Real.exp 6 = Real.exp 4 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
      ring
    rwa [h4] at h3
  have scale : ∀ X X' c : ℝ, 0 ≤ c → X ≤ Real.exp 6 * X' → c * X ≤ Real.exp 6 * (c * X') := by
    intro X X' c hc hX
    calc c * X ≤ c * (Real.exp 6 * X') := mul_le_mul_of_nonneg_left hX hc
      _ = Real.exp 6 * (c * X') := by ring
  have hC1 : (0:ℝ) ≤ phi ^ 3 * d3 := mul_nonneg (pow_nonneg hphi.le 3) hd3
  have hC2 : (0:ℝ) ≤ phi ^ 2 * d2 * beta := mul_nonneg (mul_nonneg (pow_nonneg hphi.le 2) hd2) hbeta.le
  have hC3 : (0:ℝ) ≤ phi * d1 * beta ^ 2 := mul_nonneg (mul_nonneg hphi.le hd1) (pow_nonneg hbeta.le 2)
  have hDjk : (0:ℝ) ≤ (if j = k then (1:ℝ) else 0) := by split <;> norm_num
  have hDjl : (0:ℝ) ≤ (if j = l then (1:ℝ) else 0) := by split <;> norm_num
  have hDkl : (0:ℝ) ≤ (if k = l then (1:ℝ) else 0) := by split <;> norm_num
  have hCDjk2 : (0:ℝ) ≤ phi ^ 2 * d2 * beta * (if j = k then (1:ℝ) else 0) := mul_nonneg hC2 hDjk
  have hCDjl2 : (0:ℝ) ≤ phi ^ 2 * d2 * beta * (if j = l then (1:ℝ) else 0) := mul_nonneg hC2 hDjl
  have hCDkl2 : (0:ℝ) ≤ phi ^ 2 * d2 * beta * (if k = l then (1:ℝ) else 0) := mul_nonneg hC2 hDkl
  have hCDjk3 : (0:ℝ) ≤ phi * d1 * beta ^ 2 * (if j = k then (1:ℝ) else 0) := mul_nonneg hC3 hDjk
  have hCDjl3 : (0:ℝ) ≤ phi * d1 * beta ^ 2 * (if j = l then (1:ℝ) else 0) := mul_nonneg hC3 hDjl
  have hCDkl3 : (0:ℝ) ≤ phi * d1 * beta ^ 2 * (if k = l then (1:ℝ) else 0) := mul_nonneg hC3 hDkl
  have hCDjljk3 : (0:ℝ) ≤ phi * d1 * beta ^ 2 * (if j = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0) := mul_nonneg hCDjl3 hDjk
  constructor
  · have haf : pi w j ≤ Real.exp 2 * pi (w + w') j := hratio_bwd j
    have hbf : pi w k ≤ Real.exp 2 * pi (w + w') k := hratio_bwd k
    have hcf : pi w l ≤ Real.exp 2 * pi (w + w') l := hratio_bwd l
    have m3 : pi w j * pi w k * pi w l ≤ Real.exp 6 * (pi (w + w') j * pi (w + w') k * pi (w + w') l) :=
      monomial3 (pi w j) (pi w k) (pi w l) (pi (w + w') j) (pi (w + w') k) (pi (w + w') l)
        (le_of_lt (hpipos w k)) (le_of_lt (hpipos w l))
        (le_of_lt (hpipos (w + w') j)) (le_of_lt (hpipos (w + w') k)) (le_of_lt (hpipos (w + w') l))
        haf hbf hcf
    have m2ab : pi w j * pi w k ≤ Real.exp 6 * (pi (w + w') j * pi (w + w') k) :=
      monomial2 (pi w j) (pi w k) (pi (w + w') j) (pi (w + w') k)
        (le_of_lt (hpipos w k)) (le_of_lt (hpipos (w + w') j)) (le_of_lt (hpipos (w + w') k)) haf hbf
    have m2ac : pi w j * pi w l ≤ Real.exp 6 * (pi (w + w') j * pi (w + w') l) :=
      monomial2 (pi w j) (pi w l) (pi (w + w') j) (pi (w + w') l)
        (le_of_lt (hpipos w l)) (le_of_lt (hpipos (w + w') j)) (le_of_lt (hpipos (w + w') l)) haf hcf
    have m1a : pi w j ≤ Real.exp 6 * pi (w + w') j :=
      monomial1 (pi w j) (pi (w + w') j) (le_of_lt (hpipos (w + w') j)) haf
    have hT1 := scale (pi w j * pi w k * pi w l) (pi (w + w') j * pi (w + w') k * pi (w + w') l) (phi ^ 3 * d3) hC1 m3
    have hT2 := scale (pi w j * pi w k * pi w l) (pi (w + w') j * pi (w + w') k * pi (w + w') l) (phi ^ 2 * d2 * beta) hC2 m3
    have hT3 := scale (pi w j * pi w k * pi w l) (pi (w + w') j * pi (w + w') k * pi (w + w') l) (phi * d1 * beta ^ 2) hC3 m3
    have hT4 := scale (pi w j * pi w l) (pi (w + w') j * pi (w + w') l) (phi ^ 2 * d2 * beta * (if j = k then (1:ℝ) else 0)) hCDjk2 m2ac
    have hT5 := scale (pi w j * pi w l) (pi (w + w') j * pi (w + w') l) (phi * d1 * beta ^ 2 * (if j = k then (1:ℝ) else 0)) hCDjk3 m2ac
    have hT6 := scale (pi w j * pi w k) (pi (w + w') j * pi (w + w') k) (phi ^ 2 * d2 * beta * (if j = l then (1:ℝ) else 0)) hCDjl2 m2ab
    have hT7 := scale (pi w j * pi w k) (pi (w + w') j * pi (w + w') k) (phi * d1 * beta ^ 2 * (if j = l then (1:ℝ) else 0)) hCDjl3 m2ab
    have hT8 := scale (pi w j * pi w k) (pi (w + w') j * pi (w + w') k) (phi ^ 2 * d2 * beta * (if k = l then (1:ℝ) else 0)) hCDkl2 m2ab
    have hT9 := scale (pi w j * pi w k) (pi (w + w') j * pi (w + w') k) (phi * d1 * beta ^ 2 * (if k = l then (1:ℝ) else 0)) hCDkl3 m2ab
    have hT10 := scale (pi w j) (pi (w + w') j) (phi * d1 * beta ^ 2 * (if j = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) hCDjljk3 m1a
    dsimp only [Q, W, P]
    linarith [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10]
  · have haf : pi (w + w') j ≤ Real.exp 2 * pi w j := hratio_fwd j
    have hbf : pi (w + w') k ≤ Real.exp 2 * pi w k := hratio_fwd k
    have hcf : pi (w + w') l ≤ Real.exp 2 * pi w l := hratio_fwd l
    have m3 : pi (w + w') j * pi (w + w') k * pi (w + w') l ≤ Real.exp 6 * (pi w j * pi w k * pi w l) :=
      monomial3 (pi (w + w') j) (pi (w + w') k) (pi (w + w') l) (pi w j) (pi w k) (pi w l)
        (le_of_lt (hpipos (w + w') k)) (le_of_lt (hpipos (w + w') l))
        (le_of_lt (hpipos w j)) (le_of_lt (hpipos w k)) (le_of_lt (hpipos w l))
        haf hbf hcf
    have m2ab : pi (w + w') j * pi (w + w') k ≤ Real.exp 6 * (pi w j * pi w k) :=
      monomial2 (pi (w + w') j) (pi (w + w') k) (pi w j) (pi w k)
        (le_of_lt (hpipos (w + w') k)) (le_of_lt (hpipos w j)) (le_of_lt (hpipos w k)) haf hbf
    have m2ac : pi (w + w') j * pi (w + w') l ≤ Real.exp 6 * (pi w j * pi w l) :=
      monomial2 (pi (w + w') j) (pi (w + w') l) (pi w j) (pi w l)
        (le_of_lt (hpipos (w + w') l)) (le_of_lt (hpipos w j)) (le_of_lt (hpipos w l)) haf hcf
    have m1a : pi (w + w') j ≤ Real.exp 6 * pi w j :=
      monomial1 (pi (w + w') j) (pi w j) (le_of_lt (hpipos w j)) haf
    have hT1 := scale (pi (w + w') j * pi (w + w') k * pi (w + w') l) (pi w j * pi w k * pi w l) (phi ^ 3 * d3) hC1 m3
    have hT2 := scale (pi (w + w') j * pi (w + w') k * pi (w + w') l) (pi w j * pi w k * pi w l) (phi ^ 2 * d2 * beta) hC2 m3
    have hT3 := scale (pi (w + w') j * pi (w + w') k * pi (w + w') l) (pi w j * pi w k * pi w l) (phi * d1 * beta ^ 2) hC3 m3
    have hT4 := scale (pi (w + w') j * pi (w + w') l) (pi w j * pi w l) (phi ^ 2 * d2 * beta * (if j = k then (1:ℝ) else 0)) hCDjk2 m2ac
    have hT5 := scale (pi (w + w') j * pi (w + w') l) (pi w j * pi w l) (phi * d1 * beta ^ 2 * (if j = k then (1:ℝ) else 0)) hCDjk3 m2ac
    have hT6 := scale (pi (w + w') j * pi (w + w') k) (pi w j * pi w k) (phi ^ 2 * d2 * beta * (if j = l then (1:ℝ) else 0)) hCDjl2 m2ab
    have hT7 := scale (pi (w + w') j * pi (w + w') k) (pi w j * pi w k) (phi * d1 * beta ^ 2 * (if j = l then (1:ℝ) else 0)) hCDjl3 m2ab
    have hT8 := scale (pi (w + w') j * pi (w + w') k) (pi w j * pi w k) (phi ^ 2 * d2 * beta * (if k = l then (1:ℝ) else 0)) hCDkl2 m2ab
    have hT9 := scale (pi (w + w') j * pi (w + w') k) (pi w j * pi w k) (phi * d1 * beta ^ 2 * (if k = l then (1:ℝ) else 0)) hCDkl3 m2ab
    have hT10 := scale (pi (w + w') j) (pi w j) (phi * d1 * beta ^ 2 * (if j = l then (1:ℝ) else 0) * (if j = k then (1:ℝ) else 0)) hCDjljk3 m1a
    dsimp only [Q, W, P]
    linarith [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10]
  /- @proof-region region.target-node.session.38669bc3a29403af end -/

end Statlib.Imported
end

