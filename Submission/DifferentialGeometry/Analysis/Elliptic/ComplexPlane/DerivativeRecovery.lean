import Submission.DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Multilinear
import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology _root_.NNReal
namespace DifferentialGeometry.Analysis.Elliptic

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem iteratedFDeriv_two_iteratedFDeriv_apply
    {f : E → F} {x : E} (n : ℕ) (a b : E) (v : Fin n → E) :
    iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n f) x ![a, b] v =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b v)) := by
  let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm
  have heq : fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) x =
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n f)) x) := by
    change fderiv ℝ (e ∘ fderiv ℝ (iteratedFDeriv ℝ n f)) x = _
    exact LinearIsometryEquiv.comp_fderiv
      (𝕜 := ℝ) (E := E →L[ℝ] E [×n]→L[ℝ] F) (F := E [×(n + 1)]→L[ℝ] F)
      (G := E) e (f := fderiv ℝ (iteratedFDeriv ℝ n f)) (x := x)
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_succ_apply_left, heq]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.iteratedFDeriv_two_iteratedFDeriv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.iteratedFDeriv_two_iteratedFDeriv_apply target :: scope.openDecls } }

private theorem iteratedFDeriv_two_apply_const
    {f : E → F} {x : E} {n : ℕ} (hf : ContDiffAt ℝ (n + 2) f x)
    (a b : E) (v : Fin n → E) :
    iteratedFDeriv ℝ 2 (fun y => iteratedFDeriv ℝ n f y v) x ![a, b] =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b v)) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F v
  have hT : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by norm_cast; omega)
  have h := congrArg (fun A => A ![a, b]) (L.iteratedFDeriv_comp_left hT le_rfl)
  exact h.trans (iteratedFDeriv_two_iteratedFDeriv_apply n a b v)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.iteratedFDeriv_two_apply_const
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.iteratedFDeriv_two_apply_const target :: scope.openDecls } }

private theorem laplacian_jet_recurrence
    {s : Set ℂ} (hs : IsOpen s) {f h : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 2) f s) (hΔ : _root_.Set.EqOn (Laplacian.laplacian f) h s)
    {x : ℂ} (hx : x ∈ s) (v : Fin n → ℂ) :
    iteratedFDeriv ℝ n h x v =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons 1 (Fin.cons 1 v)) +
        iteratedFDeriv ℝ (n + 2) f x (Fin.cons Complex.I (Fin.cons Complex.I v)) := by
  have he : Laplacian.laplacian f =ᶠ[𝓝 x] h := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hΔ hy
  rw [← (he.iteratedFDeriv ℝ n).eq_of_nhds,
    ← ((hf x hx).contDiffAt (hs.mem_nhds hx)).laplacian_iteratedFDeriv,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [add_apply]
  rw [iteratedFDeriv_two_iteratedFDeriv_apply, iteratedFDeriv_two_iteratedFDeriv_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.laplacian_jet_recurrence
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.laplacian_jet_recurrence target :: scope.openDecls } }

private theorem exists_perm_of_bool_count_eq
    {N : ℕ} (v w : Fin N → Bool)
    (hc : (Finset.univ.filter fun i => v i = _root_.Bool.true).card =
      (Finset.univ.filter fun i => w i = _root_.Bool.true).card) :
    ∃ σ : Equiv.Perm (Fin N), ∀ i, w (σ i) = v i := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (Finset.univ.filter fun i => v i = _root_.Bool.true) (Finset.univ.filter fun i => w i = _root_.Bool.true) hc
  refine ⟨σ, ?_⟩
  intro i
  have hm : w (σ i) = _root_.Bool.true ↔ v i = true := by
    have hmem := congrArg (fun t : Finset (Fin N) => σ i ∈ t) hσ
    simpa only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply] using Iff.of_eq hmem.symm
  cases hv : v i <;> cases hw : w (σ i) <;> simp_all

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_perm_of_bool_count_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.exists_perm_of_bool_count_eq target :: scope.openDecls } }

private def normalCount {N : ℕ} (v : Fin N → Bool) : ℕ := ∑ i, if v i then 1 else 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.normalCount
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.normalCount target :: scope.openDecls } }

private def normalTuple (N j : ℕ) : Fin N → Bool := fun i => _root_.Decidable.decide (i.val < j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.normalTuple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.normalTuple target :: scope.openDecls } }

private def complexDirection (b : Bool) : ℂ := if b then Complex.I else 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.complexDirection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.complexDirection target :: scope.openDecls } }

private theorem normalCount_le {N : ℕ} (v : Fin N → Bool) : normalCount v ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, 1 := Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = N := by simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.normalCount_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.normalCount_le target :: scope.openDecls } }

private theorem normalCount_cons {N : ℕ} (b : Bool) (v : Fin N → Bool) :
    normalCount (Fin.cons b v) = (if b then 1 else 0) + normalCount v := by
  unfold normalCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.normalCount_cons
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.normalCount_cons target :: scope.openDecls } }

private theorem normalCount_normalTuple {N j : ℕ} (hj : j ≤ N) :
    normalCount (normalTuple N j) = j := by
  induction N generalizing j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    simp [normalCount]
  | succ N ih =>
    cases j with
    | zero => simp [normalCount, normalTuple]
    | succ j =>
      have ht : normalTuple (N + 1) (j + 1) = Fin.cons _root_.Bool.true (normalTuple N j) := by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp [normalTuple]
      rw [ht, normalCount_cons, ih (by omega)]
      simp [add_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.normalCount_normalTuple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.normalCount_normalTuple target :: scope.openDecls } }

private theorem iteratedFDeriv_eq_of_normalCount_eq
    {f : ℂ → F} {x : ℂ} {N : ℕ} (hf : ContDiffAt ℝ N f x)
    {v w : Fin N → Bool} (hc : normalCount v = normalCount w) :
    iteratedFDeriv ℝ N f x (fun i => complexDirection (v i)) =
      iteratedFDeriv ℝ N f x (fun i => complexDirection (w i)) := by
  have hcard : (Finset.univ.filter fun i => v i = _root_.Bool.true).card =
      (Finset.univ.filter fun i => w i = _root_.Bool.true).card := by
    simpa only [normalCount, Finset.card_filter, Bool.cond_eq_ite] using hc
  obtain ⟨σ, hσ⟩ := exists_perm_of_bool_count_eq v w hcard
  have he := congrArg (fun A => A (fun i => complexDirection (w i))) (hf.iteratedFDeriv_perm σ)
  simpa only [ContinuousMultilinearMap.domDomCongr_apply, hσ] using he

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.iteratedFDeriv_eq_of_normalCount_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.iteratedFDeriv_eq_of_normalCount_eq target :: scope.openDecls } }

private theorem exists_holder_eval
    {X H : Type*} [PseudoEMetricSpace X] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {N : ℕ} {s : Set X} {A : X → H [×N]→L[ℝ] F} {K α : ℝ≥0}
    (hA : HolderOnWith K α A s) (v : Fin N → H) :
    ∃ C : ℝ≥0, HolderOnWith C α (fun x => A x v) s := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin N => H) F v
  refine ⟨‖L‖₊ * K, ?_⟩
  have hh := L.lipschitz.holderWith.comp_holderOnWith hA
  simpa only [Function.comp_def, one_mul, NNReal.coe_one, NNReal.rpow_one] using! hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_holder_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.exists_holder_eval target :: scope.openDecls } }

private theorem holder_sub
    {X H : Type*} [PseudoMetricSpace X] [NormedAddCommGroup H]
    {s : Set X} {a b : X → H} {K L α : ℝ≥0}
    (ha : HolderOnWith K α a s) (hb : HolderOnWith L α b s) :
    HolderOnWith (K + L) α (fun x => a x - b x) s := by
  exact HolderWith.restrict_iff.mp
    (DifferentialGeometry.Analysis.Schauder.holderWith_sub ha.holderWith hb.holderWith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.holder_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.holder_sub target :: scope.openDecls } }

private theorem exists_holderOnWith_normalTuple
    {s : Set ℂ} (hs : IsOpen s) {f h : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 2) f s) (hΔ : _root_.Set.EqOn (Laplacian.laplacian f) h s)
    {K L α : ℝ≥0} (hH : HolderOnWith K α (iteratedFDeriv ℝ n h) s)
    (hV : HolderOnWith L α
      (iteratedFDeriv ℝ 2 (fun z => iteratedFDeriv ℝ n f z (fun _ => (1 : ℂ)))) s) :
    ∀ j ≤ n + 2, ∃ C : ℝ≥0, HolderOnWith C α
      (fun z => iteratedFDeriv ℝ (n + 2) f z
        (fun i => complexDirection (normalTuple (n + 2) j i))) s := by
  have hfa (x : ℂ) (hx : x ∈ s) : ContDiffAt ℝ (n + 2 : ℕ) f x := by
    simpa using (hf x hx).contDiffAt (hs.mem_nhds hx)
  have hbase (a b : Bool) : ∃ C : ℝ≥0, HolderOnWith C α
      (fun z => iteratedFDeriv ℝ (n + 2) f z
        (fun i => complexDirection ((Fin.cons a (Fin.cons b (fun _ : Fin n => _root_.Bool.false)) : Fin (n + 2) → Bool) i))) s := by
    obtain ⟨C, hC⟩ := exists_holder_eval hV ![complexDirection a, complexDirection b]
    have he (z : ℂ) (hz : z ∈ s) :
        iteratedFDeriv ℝ 2 (fun z => iteratedFDeriv ℝ n f z (fun _ => (1 : ℂ))) z
          ![complexDirection a, complexDirection b] =
        iteratedFDeriv ℝ (n + 2) f z
          (fun i => complexDirection ((Fin.cons a (Fin.cons b (fun _ : Fin n => _root_.Bool.false)) : Fin (n + 2) → Bool) i)) := by
      rw [iteratedFDeriv_two_apply_const (hfa z hz)]
      congr 1
      ext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> rfl
    refine ⟨C, ?_⟩
    intro x hx y hy
    dsimp only
    rw [← he x hx, ← he y hy]
    exact hC x hx y hy
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hj2 : j ≤ 2
    · let a : Bool := _root_.Decidable.decide (0 < j)
      let b : Bool := _root_.Decidable.decide (1 < j)
      obtain ⟨C, hC⟩ := hbase a b
      have hc : normalCount (normalTuple (n + 2) j) =
          normalCount (Fin.cons a (Fin.cons b (fun _ : Fin n => _root_.Bool.false))) := by
        rw [normalCount_normalTuple hj, normalCount_cons, normalCount_cons]
        simp [a, b, normalCount]
        split_ifs <;> omega
      refine ⟨C, ?_⟩
      intro x hx y hy
      dsimp only
      rw [iteratedFDeriv_eq_of_normalCount_eq (hfa x hx) hc,
        iteratedFDeriv_eq_of_normalCount_eq (hfa y hy) hc]
      exact hC x hx y hy
    · have hj3 : 3 ≤ j := by omega
      have hjn : j - 2 ≤ n := by omega
      let t := normalTuple n (j - 2)
      have hct : normalCount t = j - 2 := normalCount_normalTuple hjn
      have hc1 : normalCount (Fin.cons _root_.Bool.false (Fin.cons _root_.Bool.false t)) =
          normalCount (normalTuple (n + 2) (j - 2)) := by
        rw [normalCount_cons, normalCount_cons, hct, normalCount_normalTuple (by omega)]
        simp
      have hcI : normalCount (normalTuple (n + 2) j) =
          normalCount (Fin.cons _root_.Bool.true (Fin.cons _root_.Bool.true t)) := by
        rw [normalCount_normalTuple hj, normalCount_cons, normalCount_cons, hct]
        simp only [↓reduceIte]
        omega
      obtain ⟨A, hA⟩ := ih (j - 2) (by omega) (by omega)
      obtain ⟨B, hB⟩ := exists_holder_eval hH (fun i => complexDirection (t i))
      have hlow : HolderOnWith A α
          (fun z => iteratedFDeriv ℝ (n + 2) f z
            (Fin.cons 1 (Fin.cons 1 (fun i => complexDirection (t i))))) s := by
        intro x hx y hy
        dsimp only
        have hc (z : ℂ) (hz : z ∈ s) :=
          iteratedFDeriv_eq_of_normalCount_eq (hfa z hz) hc1
        have hdir : (fun i => complexDirection ((Fin.cons _root_.Bool.false (Fin.cons _root_.Bool.false t) : Fin (n + 2) → Bool) i)) =
            Fin.cons 1 (Fin.cons 1 (fun i => complexDirection (t i))) := by
          ext i
          refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> rfl
        rw [← hdir, hc x hx, hc y hy]
        exact hA x hx y hy
      have hrec (z : ℂ) (hz : z ∈ s) :
          iteratedFDeriv ℝ (n + 2) f z
            (fun i => complexDirection (normalTuple (n + 2) j i)) =
          iteratedFDeriv ℝ n h z (fun i => complexDirection (t i)) -
            iteratedFDeriv ℝ (n + 2) f z
              (Fin.cons 1 (Fin.cons 1 (fun i => complexDirection (t i)))) := by
        rw [iteratedFDeriv_eq_of_normalCount_eq (hfa z hz) hcI]
        have hh := laplacian_jet_recurrence hs hf hΔ hz (fun i => complexDirection (t i))
        rw [hh]
        have hdir : (fun i => complexDirection ((Fin.cons _root_.Bool.true (Fin.cons _root_.Bool.true t) : Fin (n + 2) → Bool) i)) =
            Fin.cons Complex.I (Fin.cons Complex.I (fun i => complexDirection (t i))) := by
          ext i
          refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;> rfl
        rw [hdir]
        abel
      refine ⟨B + A, ?_⟩
      intro x hx y hy
      dsimp only
      rw [hrec x hx, hrec y hy]
      exact holder_sub hB hlow x hx y hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_holderOnWith_normalTuple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.exists_holderOnWith_normalTuple target :: scope.openDecls } }

theorem exists_holderOnWith_iteratedFDeriv_of_laplacian_tangent
    {s : Set ℂ} (hs : IsOpen s) {f h : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 2) f s) (hΔ : _root_.Set.EqOn (Laplacian.laplacian f) h s)
    {K L α : ℝ≥0} (hH : HolderOnWith K α (iteratedFDeriv ℝ n h) s)
    (hV : HolderOnWith L α
      (iteratedFDeriv ℝ 2 (fun z => iteratedFDeriv ℝ n f z (fun _ => (1 : ℂ)))) s) :
    ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ (n + 2) f) s := by
  apply DifferentialGeometry.Analysis.Schauder.exists_holderOnWith_continuousMultilinearMap_of_basis
    Complex.basisOneI
  intro v
  let w : Fin (n + 2) → Bool := fun i => _root_.Decidable.decide (v i = 1)
  obtain ⟨C, hC⟩ := exists_holderOnWith_normalTuple hs hf hΔ hH hV (normalCount w) (normalCount_le w)
  have he (z : ℂ) (hz : z ∈ s) :
      iteratedFDeriv ℝ (n + 2) f z (fun i => Complex.basisOneI (v i)) =
        iteratedFDeriv ℝ (n + 2) f z
          (fun i => complexDirection (normalTuple (n + 2) (normalCount w) i)) := by
    have hw : (fun i => Complex.basisOneI (v i)) = fun i => complexDirection (w i) := by
      ext i
      generalize hv : v i = t
      fin_cases t <;> simp [w, complexDirection, hv, Complex.basisOneI]
    rw [hw]
    apply iteratedFDeriv_eq_of_normalCount_eq (by simpa using (hf z hz).contDiffAt (hs.mem_nhds hz))
    exact (normalCount_normalTuple (normalCount_le w)).symm
  refine ⟨C, ?_⟩
  intro x hx y hy
  dsimp only
  rw [he x hx, he y hy]
  exact hC x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_holderOnWith_iteratedFDeriv_of_laplacian_tangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_holderOnWith_iteratedFDeriv_of_laplacian_tangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_holderOnWith_iteratedFDeriv_of_laplacian_tangent ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_holderOnWith_iteratedFDeriv_of_laplacian_tangent

end DifferentialGeometry.Analysis.Elliptic
