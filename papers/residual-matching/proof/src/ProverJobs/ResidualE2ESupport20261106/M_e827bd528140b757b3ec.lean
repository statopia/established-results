import Lean
import ProverJobs.ResidualE2ESupport20261106.M_da1e2a812640d525bb1a
import ProverJobs.ResidualE2ESupport20261106.M_d2863c7273476f37a053
import ProverJobs.ResidualE2ESupport20261106.M_197a70b8ffe772044e0f

namespace PaperProofTasks.ResidualE2ESupport20261106
open MeasureTheory ProbabilityTheory
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))
open _root_.PaperProofTasks.ResidualE2ESupport20261106.Statlib.Imported

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib))
run_cmd do
  if (← _root_.Lean.MonadEnv.getEnv).isNamespace `Statlib.Imported then
    _root_.Lean.Elab.Command.elabCommand (← `(command| open _root_.Statlib.Imported))

set_option autoImplicit false in
theorem statopia_math_node_1598762335_905f24e9 : ∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hnm : n ≤ m)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hAint : ∀ (i : Fin m) (j : Fin n), MeasureTheory.Integrable (fun ω => A ω i j) μ)
    (hAmean : ∀ (i : Fin m) (j : Fin n), ∫ ω, A ω i j ∂μ = 0)
    (hAcov : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      ∫ ω, A ω i j * A ω k l ∂μ = if (i, j) = (k, l) then 1 / (m : ℝ) else 0)
    (hAprodint : ∀ (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n),
      MeasureTheory.Integrable (fun ω => A ω i j * A ω k l) μ)
    (S2 : Matrix (Fin (m + n)) (Fin (m + n)) ℂ)
    (hS2herm : S2.IsHermitian)
    (hS2 : ∀ (a b : Fin (m + n)), S2 a b = ∫ ω,
      ∑ c : Fin (m + n),
        ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) a c
        * ((Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
            (Matrix.map (A ω) Complex.ofReal)
            (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
            (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) c b ∂μ),
    sSup (Set.range fun q : Fin (m + n) => |(hS2herm.eigenvalues q)|) = 1 := by
  /- @proof-region region.target-node.session.074c31491cb6cda3 begin -/
  intro m n hm hn hnm Ω _ μ _ A hAint hAmean hAcov hAprodint S2 hS2herm hS2
  let D : Ω → Matrix (Fin (m + n)) (Fin (m + n)) ℂ := fun ω =>
    (Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ)
      (Matrix.map (A ω) Complex.ofReal)
      (Matrix.transpose (Matrix.map (A ω) Complex.ofReal))
      (0 : Matrix (Fin n) (Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  let w : Fin m ⊕ Fin n → ℝ := Sum.elim (fun _ => (n : ℝ) / (m : ℝ)) (fun _ => 1)
  have hD_ll : ∀ (ω : Ω) (i k : Fin m),
      D ω (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl k)) = 0 := by
    intro ω i k
    simp [D, Matrix.submatrix_apply, Matrix.fromBlocks]
  have hD_lr : ∀ (ω : Ω) (i : Fin m) (j : Fin n),
      D ω (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = (A ω i j : ℂ) := by
    intro ω i j
    simp [D, Matrix.submatrix_apply, Matrix.fromBlocks]
  have hD_rl : ∀ (ω : Ω) (j : Fin n) (i : Fin m),
      D ω (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl i)) = (A ω i j : ℂ) := by
    intro ω j i
    simp [D, Matrix.submatrix_apply, Matrix.fromBlocks]
  have hD_rr : ∀ (ω : Ω) (j l : Fin n),
      D ω (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inr l)) = 0 := by
    intro ω j l
    simp [D, Matrix.submatrix_apply, Matrix.fromBlocks]
  have hquad : ∀ (s t : Fin m ⊕ Fin n),
      S2 (finSumFinEquiv s) (finSumFinEquiv t) =
        ∫ ω, ∑ u : Fin m ⊕ Fin n,
          D ω (finSumFinEquiv s) (finSumFinEquiv u)
            * D ω (finSumFinEquiv u) (finSumFinEquiv t) ∂μ := by
    intro s t
    rw [hS2 (finSumFinEquiv s) (finSumFinEquiv t)]
    congr 1
    funext ω
    exact (Equiv.sum_comp finSumFinEquiv
      (fun c : Fin (m + n) =>
        D ω (finSumFinEquiv s) c * D ω c (finSumFinEquiv t))).symm
  have hval_lr : ∀ (i : Fin m) (j : Fin n),
      S2 (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = 0 := by
    intro i j
    rw [hquad (Sum.inl i) (Sum.inr j)]
    have hz : (fun ω : Ω => ∑ u : Fin m ⊕ Fin n,
        D ω (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv u)
          * D ω (finSumFinEquiv u) (finSumFinEquiv (Sum.inr j)))
        = fun _ => (0 : ℂ) := by
      funext ω
      apply Finset.sum_eq_zero
      intro u _
      cases u with
      | inl a => rw [hD_ll ω i a]; simp
      | inr b => rw [hD_rr ω b j]; simp
    rw [hz]
    simp
  have hval_rl : ∀ (j : Fin n) (i : Fin m),
      S2 (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl i)) = 0 := by
    intro j i
    rw [hquad (Sum.inr j) (Sum.inl i)]
    have hz : (fun ω : Ω => ∑ u : Fin m ⊕ Fin n,
        D ω (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv u)
          * D ω (finSumFinEquiv u) (finSumFinEquiv (Sum.inl i)))
        = fun _ => (0 : ℂ) := by
      funext ω
      apply Finset.sum_eq_zero
      intro u _
      cases u with
      | inl a => rw [hD_ll ω a i]; simp
      | inr b => rw [hD_rr ω j b]; simp
    rw [hz]
    simp
  have hcast_sum : ∀ (ι : Type) [DecidableEq ι] (s : Finset ι) (g : ι → ℝ),
      ((s.sum g : ℝ) : ℂ) = s.sum (fun j => (g j : ℂ)) := by
    intro ι _ s g
    refine Finset.induction ?_ ?_ s
    · simp
    · intro a t ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [Complex.ofReal_add, ih]
  have hval_ll : ∀ (i k : Fin m),
      S2 (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl k))
        = ((if i = k then (n : ℝ) / (m : ℝ) else 0 : ℝ) : ℂ) := by
    intro i k
    rw [hquad (Sum.inl i) (Sum.inl k)]
    have hfun : (fun ω : Ω => ∑ u : Fin m ⊕ Fin n,
        D ω (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv u)
          * D ω (finSumFinEquiv u) (finSumFinEquiv (Sum.inl k)))
        = fun ω => ((∑ j : Fin n, A ω i j * A ω k j : ℝ) : ℂ) := by
      funext ω
      rw [Fintype.sum_sum_type]
      rw [show (∑ a : Fin m, D ω (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl a))
            * D ω (finSumFinEquiv (Sum.inl a)) (finSumFinEquiv (Sum.inl k))) = 0 from by
        apply Finset.sum_eq_zero
        intro a _
        rw [hD_ll ω i a]
        simp]
      rw [zero_add]
      rw [show (∑ b : Fin n, D ω (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr b))
            * D ω (finSumFinEquiv (Sum.inr b)) (finSumFinEquiv (Sum.inl k)))
          = ∑ b : Fin n, ((A ω i b * A ω k b : ℝ) : ℂ) from by
        apply Finset.sum_congr rfl
        intro b _
        rw [hD_lr ω i b, hD_rl ω b k, ← Complex.ofReal_mul]]
      exact (hcast_sum (Fin n) Finset.univ (fun j => A ω i j * A ω k j)).symm
    rw [hfun, integral_complex_ofReal (μ := μ) (f := fun ω : Ω => ∑ j : Fin n, A ω i j * A ω k j)]
    congr 1
    rw [integral_finset_sum Finset.univ (fun j _ => hAprodint i j k j)]
    simp only [hAcov]
    by_cases hik : i = k
    · subst hik
      simp [div_eq_mul_inv]
    · have hsum : (∑ j : Fin n, (if (i, j) = (k, j) then (1 : ℝ) / (m : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact if_neg (fun h => hik (congrArg Prod.fst h))
      rw [hsum]
      exact (if_neg hik).symm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hval_rr : ∀ (j l : Fin n),
      S2 (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inr l))
        = ((if j = l then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    intro j l
    rw [hquad (Sum.inr j) (Sum.inr l)]
    have hfun : (fun ω : Ω => ∑ u : Fin m ⊕ Fin n,
        D ω (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv u)
          * D ω (finSumFinEquiv u) (finSumFinEquiv (Sum.inr l)))
        = fun ω => ((∑ i : Fin m, A ω i j * A ω i l : ℝ) : ℂ) := by
      funext ω
      rw [Fintype.sum_sum_type]
      rw [show (∑ b : Fin n, D ω (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inr b))
            * D ω (finSumFinEquiv (Sum.inr b)) (finSumFinEquiv (Sum.inr l))) = 0 from by
        apply Finset.sum_eq_zero
        intro b _
        rw [hD_rr ω j b]
        simp]
      rw [add_zero]
      rw [show (∑ a : Fin m, D ω (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl a))
            * D ω (finSumFinEquiv (Sum.inl a)) (finSumFinEquiv (Sum.inr l)))
          = ∑ a : Fin m, ((A ω a j * A ω a l : ℝ) : ℂ) from by
        apply Finset.sum_congr rfl
        intro a _
        rw [hD_rl ω j a, hD_lr ω a l, ← Complex.ofReal_mul]]
      exact (hcast_sum (Fin m) Finset.univ (fun a => A ω a j * A ω a l)).symm
    rw [hfun, integral_complex_ofReal (μ := μ) (f := fun ω : Ω => ∑ i : Fin m, A ω i j * A ω i l)]
    congr 1
    rw [integral_finset_sum Finset.univ (fun a _ => hAprodint a j a l)]
    simp only [hAcov]
    by_cases hjl : j = l
    · subst hjl
      simp [hm0]
    · have hsum : (∑ a : Fin m, (if (a, j) = (a, l) then (1 : ℝ) / (m : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        exact if_neg (fun h => hjl (congrArg Prod.snd h))
      rw [hsum]
      exact (if_neg hjl).symm
  let vR : Fin (m + n) → ℝ := fun q => w (finSumFinEquiv.symm q)
  have hdiagentry : ∀ a b : Fin (m + n), S2 a b = if a = b then ((vR a : ℝ) : ℂ) else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective a
      rw [if_pos rfl]
      rcases s with i | j
      · rw [hval_ll i i, if_pos rfl]
        simp only [vR, Equiv.symm_apply_apply]
        simp [w]
      · rw [hval_rr j j, if_pos rfl]
        simp only [vR, Equiv.symm_apply_apply]
        simp [w]
    · obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective a
      obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective b
      rw [if_neg hab]
      rcases s with i | j <;> rcases t with k | l
      · have hik : ¬ i = k := fun h => hab (by rw [h])
        rw [hval_ll i k, if_neg hik]
        simp
      · rw [hval_lr i l]
      · rw [hval_rl j k]
      · have hjl : ¬ j = l := fun h => hab (by rw [h])
        rw [hval_rr j l, if_neg hjl]
        simp
  have hrange : Set.range hS2herm.eigenvalues = Set.range vR :=
    statopia_math_node_3272233362_d4716ab0 S2 hS2herm vR hdiagentry
  have hvR_abs_le : ∀ q : Fin (m + n), |vR q| ≤ 1 := by
    intro q
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective q
    rcases s with i | j
    · have h4 : (0 : ℝ) ≤ (n : ℝ) / (m : ℝ) := div_nonneg (by positivity) (le_of_lt hmpos)
      have h3 : (n : ℝ) / (m : ℝ) ≤ 1 := by
        rw [div_le_one hmpos]
        exact_mod_cast hnm
      simp only [vR, Equiv.symm_apply_apply, w, Sum.elim_inl]
      rw [abs_of_nonneg h4]
      exact h3
    · simp [vR, w]
  have hbound : ∀ q : Fin (m + n), |hS2herm.eigenvalues q| ≤ 1 := by
    intro q
    have hx : hS2herm.eigenvalues q ∈ Set.range vR := by
      rw [← hrange]
      exact ⟨q, rfl⟩
    obtain ⟨t, ht⟩ := hx
    rw [← ht]
    exact hvR_abs_le t
  have hn0 : 0 < n := by omega
  have hvR_one : vR (finSumFinEquiv (Sum.inr ⟨0, hn0⟩)) = 1 := by
    simp only [vR, Equiv.symm_apply_apply]
    simp [w]
  have hmem_one : (1 : ℝ) ∈ Set.range (fun q : Fin (m + n) => |hS2herm.eigenvalues q|) := by
    have hmem : (1 : ℝ) ∈ Set.range vR := ⟨_, hvR_one⟩
    rw [← hrange] at hmem
    obtain ⟨q, hq⟩ := hmem
    refine ⟨q, ?_⟩
    show |hS2herm.eigenvalues q| = 1
    rw [hq]
    norm_num
  have hne : (Set.range fun q : Fin (m + n) => |hS2herm.eigenvalues q|).Nonempty :=
    ⟨1, hmem_one⟩
  have hbdd : BddAbove (Set.range fun q : Fin (m + n) => |hS2herm.eigenvalues q|) :=
    ⟨1, by rintro x ⟨q, rfl⟩; exact hbound q⟩
  have hub : sSup (Set.range fun q : Fin (m + n) => |hS2herm.eigenvalues q|) ≤ 1 := by
    apply Real.sSup_le
    · rintro x ⟨q, rfl⟩
      exact hbound q
    · norm_num
  have hlb : 1 ≤ sSup (Set.range fun q : Fin (m + n) => |hS2herm.eigenvalues q|) :=
    (Real.isLUB_sSup hne hbdd).1 hmem_one
  exact le_antisymm hub hlb
  /- @proof-region region.target-node.session.074c31491cb6cda3 end -/

end Statlib.Imported

