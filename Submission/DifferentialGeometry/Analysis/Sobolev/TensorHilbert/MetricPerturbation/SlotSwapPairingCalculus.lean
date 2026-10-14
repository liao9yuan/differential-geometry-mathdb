import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Commutation.CovariantDivergence
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SlotInsertion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private lemma cons_cons_comp_swap01 {α : Type*} {t : ℕ} (a b : α) (m : Fin t → α) :
    (fun k : Fin (t + 2) =>
        (Fin.cons a (Fin.cons b m) : Fin (t + 2) → α)
          ((Equiv.swap (0 : Fin (t + 2)) (1 : Fin (t + 2))) k)) =
      Fin.cons b (Fin.cons a m) := by
  funext k
  refine Fin.cases ?_ (fun k' => ?_) k
  · rw [Equiv.swap_apply_left]
    rfl
  · refine Fin.cases ?_ (fun k'' => ?_) k'
    · rw [show ((0 : Fin (t + 1)).succ) = (1 : Fin (t + 2)) from rfl, Equiv.swap_apply_right]
      rfl
    · have hne0 : (k''.succ.succ : Fin (t + 2)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (k''.succ.succ : Fin (t + 2)) ≠ 1 := by
        rw [show (1 : Fin (t + 2)) = (0 : Fin (t + 1)).succ from rfl]
        exact fun h => Fin.succ_ne_zero k'' (Fin.succ_injective _ h)
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
      rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.cons_cons_comp_swap01
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.cons_cons_comp_swap01 target :: scope.openDecls } }

private lemma comp_decomposeFin_symm_zero {α : Type*} {s : ℕ} (σ : Equiv.Perm (Fin s))
    (w : Fin (s + 1) → α) :
    (fun k : Fin (s + 1) => w ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
      Fin.cons (w 0) (fun j : Fin s => Matrix.vecTail w (σ j)) := by
  funext k
  refine Fin.cases ?_ (fun k' => ?_) k
  · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    rfl
  · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.comp_decomposeFin_symm_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.comp_decomposeFin_symm_zero target :: scope.openDecls } }

private lemma cons_cons_comp_decomposeFin_double {α : Type*} {t : ℕ}
    (tau : Equiv.Perm (Fin (t + 2))) (a b : α) (v : Fin (t + 2) → α) :
    (fun k : Fin (t + 4) =>
        (Fin.cons a (Fin.cons b v) : Fin (t + 4) → α)
          ((Equiv.Perm.decomposeFin.symm
            (0, Equiv.Perm.decomposeFin.symm (0, tau))) k)) =
      Fin.cons a (Fin.cons b (fun j => v (tau j))) := by
  funext k
  refine Fin.cases ?_ (fun k' => ?_) k
  · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    rfl
  · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    simp only [Equiv.refl_apply, Fin.cons_succ]
    refine Fin.cases ?_ (fun k'' => ?_) k'
    · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
      rfl
    · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
      simp only [Equiv.refl_apply, Fin.cons_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.cons_cons_comp_decomposeFin_double
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.cons_cons_comp_decomposeFin_double target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem unitModel_homTensorRSFieldApply_swap_eq_domDomCongr
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (m : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b m)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a m)))
    (U : SmoothCcTensor g 0 (t + 2)) (y : M) :
    unitModel (I := I) (M := M) g (t + 2)
      (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) y =
      ContinuousMultilinearMap.domDomCongr
        (Equiv.swap (0 : Fin (t + 2)) (1 : Fin (t + 2)))
        (unitModel (I := I) (M := M) g (t + 2) U y) := by
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show w = Fin.cons (w 0) (Matrix.vecTail w) from (Fin.cons_self_tail w).symm]
  rw [show (Matrix.vecTail w) = Fin.cons (Matrix.vecTail w 0) (Matrix.vecTail (Matrix.vecTail w))
    from (Fin.cons_self_tail (Matrix.vecTail w)).symm]
  rw [cons_cons_comp_swap01 (w 0) (Matrix.vecTail w 0) (Matrix.vecTail (Matrix.vecTail w))]
  exact hF y (U.toSection y) (unitTensor (I := I) (M := M) y) (w 0) (Matrix.vecTail w 0)
    (Matrix.vecTail (Matrix.vecTail w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.unitModel_homTensorRSFieldApply_swap_eq_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.unitModel_homTensorRSFieldApply_swap_eq_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.unitModel_homTensorRSFieldApply_swap_eq_domDomCongr ``Submission.DifferentialGeometry.Analysis.Sobolev.unitModel_homTensorRSFieldApply_swap_eq_domDomCongr

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma homTensorRSFieldApply_add_right_cc (g : SmoothRiemannianMetric I M) (a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) 0 a c I) (A B : SmoothCcTensor g 0 a) :
    homTensorRSFieldApply (I := I) (M := M) g 0 a c Q (A + B) =
      homTensorRSFieldApply (I := I) (M := M) g 0 a c Q A + homTensorRSFieldApply (I := I) (M := M)
        g 0 a c Q B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g 0 a c Q A +
      homTensorRSFieldApply (I := I) (M := M) g 0 a c Q B).toSection x) =
    (homTensorRSFieldApply (I := I) (M := M) g 0 a c Q A).toSection x +
      (homTensorRSFieldApply (I := I) (M := M) g 0 a c Q B).toSection x from rfl]
  rw [homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection]
  rw [show ((A + B).toSection x : TensorRSSpace 0 a I x) = A.toSection x + B.toSection x from rfl]
  exact ContinuousLinearMap.map_add _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_add_right_cc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_add_right_cc target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem homTensorRSFieldApply_swap_norm_eq (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (m : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b m)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a m)))
    (U : SmoothCcTensor g 0 (t + 2)) :
    ‖homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U‖ = ‖U‖ := by
  classical
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (t + 2) x
          ((homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 (t + 2) x (U.toSection x) := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr
      (I := I) (M := M) g (t + 2) (Equiv.swap (0 : Fin (t + 2)) (1 : Fin (t + 2))) U
      (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U)
      (fun y => unitModel_homTensorRSFieldApply_swap_eq_domDomCongr (I := I) (M := M) g t F hF U y)
      0 x
    simpa only [iteratedCovGrad_zero] using h
  have hsq : ‖homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U‖ ^ 2 = ‖U‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M), SmoothCcTensor.norm_def (I := I) (M := M),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0 (t + 2)
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0 (t + 2) U]
    exact _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have h1 : (0 : ℝ) ≤ ‖homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U‖ :=
    norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖U‖ := norm_nonneg _
  rw [← Real.sqrt_sq h1, ← Real.sqrt_sq h2, hsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_norm_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_norm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_norm_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_norm_eq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem homTensorRSFieldApply_swap_involutive (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (m : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b m)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a m)))
    (U : SmoothCcTensor g 0 (t + 2)) :
    homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) = U := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [unitModel_homTensorRSFieldApply_swap_eq_domDomCongr (I := I) (M := M) g t F hF
    (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) x]
  rw [unitModel_homTensorRSFieldApply_swap_eq_domDomCongr (I := I) (M := M) g t F hF U x]
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  rw [Equiv.swap_apply_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_involutive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_involutive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_involutive ``Submission.DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_involutive

omit [NeZero (Module.finrank ℝ E)] in
theorem homTensorRSFieldApply_swap_l2Inner_hop (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (m : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b m)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a m)))
    (A B : SmoothCcTensor g 0 (t + 2)) :
    tensorL2Inner (I := I) (M := M) g 0 (t + 2)
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F A).toFun B.toFun =
      tensorL2Inner (I := I) (M := M) g 0 (t + 2)
        A.toFun (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B).toFun := by
  have hinner1 := SmoothCcTensor.inner_def (I := I) (M := M)
    (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F A) B
  have hinner2 := SmoothCcTensor.inner_def (I := I) (M := M)
    A (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B)
  rw [← hinner1, ← hinner2]
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  have hsum : homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F A + B =
      homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F
        (A + homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B) := by
    rw [homTensorRSFieldApply_add_right_cc (I := I) (M := M) g (t + 2) (t + 2) F A
      (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B)]
    rw [homTensorRSFieldApply_swap_involutive (I := I) (M := M) g t F hF B]
  rw [hsum]
  rw [homTensorRSFieldApply_swap_norm_eq (I := I) (M := M) g t F hF
    (A + homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F B)]
  rw [homTensorRSFieldApply_swap_norm_eq (I := I) (M := M) g t F hF A]
  rw [homTensorRSFieldApply_swap_norm_eq (I := I) (M := M) g t F hF B]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_l2Inner_hop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_l2Inner_hop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_l2Inner_hop ``Submission.DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_l2Inner_hop

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem unitModel_covGrad_of_unitModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (y : M) :
    unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s S') y =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ))
        (unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s S) y) := by
  classical
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel, unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s S' y
    (unitTensor (I := I) (M := M) y) w]
  rw [comp_decomposeFin_symm_zero σ w]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s S y
    (unitTensor (I := I) (M := M) y)
    (Fin.cons (w 0) (fun j : Fin s => Matrix.vecTail w (σ j)))]
  rw [show Matrix.vecTail (Fin.cons (w 0) (fun j : Fin s => Matrix.vecTail w (σ j))
      : Fin (s + 1) → E) = (fun j : Fin s => Matrix.vecTail w (σ j)) from by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]]
  rw [show (Fin.cons (w 0) (fun j : Fin s => Matrix.vecTail w (σ j))
      : Fin (s + 1) → E) 0 = w 0 from rfl]
  have h := tensorCovDerivAt_unit_toModel_domDomCongr_of_section (I := I) (M := M)
    g s σ S S' hSS' y
      ((tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (w 0))
  have happ := congrArg (fun T : ContinuousMultilinearMap ℝ
    (fun _ : Fin s => TangentSpace I y) ℝ => T (Matrix.vecTail w)) h
  exact happ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.unitModel_covGrad_of_unitModel_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.unitModel_covGrad_of_unitModel_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.unitModel_covGrad_of_unitModel_domDomCongr ``Submission.DifferentialGeometry.Analysis.Sobolev.unitModel_covGrad_of_unitModel_domDomCongr

omit [SigmaCompactSpace M] in
theorem homTensorRSFieldApply_swap_rawConnLap_comm (g : SmoothRiemannianMetric I M) (t : ℕ)
    (F : HomTensorRSField (E := E) (M := M) 0 (t + 2) (t + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (t + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (m : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from
            (show TensorRSSpace 0 (t + 2) I x →L[ℝ] TensorRSSpace 0 (t + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b m)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
          (Fin.cons b (Fin.cons a m)))
    (U : SmoothCcTensor g 0 (t + 2)) :
    rawTensorConnLapSmooth (I := I) g 0 (t + 2)
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) =
      homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F
        (rawTensorConnLapSmooth (I := I) g 0 (t + 2) U) := by
  classical
  set tau : Equiv.Perm (Fin (t + 2)) := Equiv.swap (0 : Fin (t + 2)) (1 : Fin (t + 2)) with htau
  set tau1 : Equiv.Perm (Fin (t + 3)) := Equiv.Perm.decomposeFin.symm (0, tau) with htau1
  set tau2 : Equiv.Perm (Fin (t + 4)) := Equiv.Perm.decomposeFin.symm (0, tau1) with htau2
  have h0 : ∀ y : M, unitModel (I := I) (M := M) g (t + 2)
      (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) y =
      ContinuousMultilinearMap.domDomCongr tau (unitModel (I := I) (M := M) g (t + 2) U y) :=
    fun y => unitModel_homTensorRSFieldApply_swap_eq_domDomCongr (I := I) (M := M) g t F hF U y
  have h1 : ∀ y : M, unitModel (I := I) (M := M) g (t + 3)
      (covGrad (I := I) (M := M) g 0 (t + 2)
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U)) y =
      ContinuousMultilinearMap.domDomCongr tau1
        (unitModel (I := I) (M := M) g (t + 3)
          (covGrad (I := I) (M := M) g 0 (t + 2) U) y) :=
    fun y => unitModel_covGrad_of_unitModel_domDomCongr (I := I) (M := M) g (t + 2) tau
      U (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) h0 y
  have h2 : ∀ y : M, unitModel (I := I) (M := M) g (t + 4)
      (covGrad (I := I) (M := M) g 0 (t + 3)
        (covGrad (I := I) (M := M) g 0 (t + 2)
          (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U))) y =
      ContinuousMultilinearMap.domDomCongr tau2
        (unitModel (I := I) (M := M) g (t + 4)
          (covGrad (I := I) (M := M) g 0 (t + 3)
            (covGrad (I := I) (M := M) g 0 (t + 2) U)) y) :=
    fun y => unitModel_covGrad_of_unitModel_domDomCongr (I := I) (M := M) g (t + 3) tau1
      (covGrad (I := I) (M := M) g 0 (t + 2) U)
      (covGrad (I := I) (M := M) g 0 (t + 2)
        (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U)) h1 y
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_rawConnLap_eq_frame_sum_covariantTensor (I := I) g (t + 2)
    (homTensorRSFieldApply (I := I) (M := M) g 0 (t + 2) (t + 2) F U) x v]
  rw [unitModel_homTensorRSFieldApply_swap_eq_domDomCongr (I := I) (M := M) g t F hF
    (rawTensorConnLapSmooth (I := I) g 0 (t + 2) U) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel_rawConnLap_eq_frame_sum_covariantTensor (I := I) g (t + 2) U x (fun k => v (tau k))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h2x := congrArg
    (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin (t + 4) => E) ℝ =>
      T (Fin.cons
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (smoothOrthoFrame (I := I) g x i x))
        (Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x i x))
          (fun j => (v j : E))))) (h2 x)
  simp only [ContinuousMultilinearMap.domDomCongr_apply] at h2x
  rw [cons_cons_comp_decomposeFin_double tau
    (tangentSpaceModelContinuousLinearEquiv (I := I) x
      (smoothOrthoFrame (I := I) g x i x))
    (tangentSpaceModelContinuousLinearEquiv (I := I) x
      (smoothOrthoFrame (I := I) g x i x))
    (fun j => (v j : E))] at h2x
  exact h2x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_rawConnLap_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_rawConnLap_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_rawConnLap_comm ``Submission.DifferentialGeometry.Analysis.Sobolev.homTensorRSFieldApply_swap_rawConnLap_comm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem unitModel_operatorFieldApplication_slotInsertEndoCc_cons
    (g : SmoothRiemannianMetric I M) (s' : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (U : SmoothCcTensor g 0 (s' + 1)) (x : M) (a : E)
    (rest : Fin s' → E) :
    unitModel (I := I) (M := M) g (s' + 1)
        (operatorFieldApply (I := I) (M := M) g (s' + 1) (s' + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ) U) x
        (Fin.cons a rest) =
      unitModel (I := I) (M := M) g (s' + 1) U x
        (Fin.cons (tangentLinearMapToModel (I := I) (Λ x) a) rest) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace (s' + 1) I x →L[ℝ] Tensor0SSpace (s' + 1) I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 1) I x from
          U.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace (s' + 1) I x →L[ℝ] Tensor0SSpace (s' + 1) I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 1) I x from
          U.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [slotInsertEndoCc_toSection (I := I) (M := M) g s' Λ x]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (s' + 1) 0 x (Λ x)]
  unfold unitModel
  congr 1
  rw [show (Fin.cons a rest : Fin (s' + 1) → E) 0 = a from rfl]
  exact Fin.update_cons_zero _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotInsertEndoCc_cons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotInsertEndoCc_cons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotInsertEndoCc_cons ``Submission.DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotInsertEndoCc_cons

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem unitModel_operatorFieldApplication_slotExtend_slotInsertEndoCc_cons
    (g : SmoothRiemannianMetric I M) (s' : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (U : SmoothCcTensor g 0 (s' + 2)) (x : M) (a b : E)
    (m : Fin s' → E) :
    unitModel (I := I) (M := M) g (s' + 2)
        (operatorFieldApply (I := I) (M := M) g (s' + 2) (s' + 2)
          (slotExtend (I := I) (M := M) g (s' + 1) (s' + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ)) U) x
        (Fin.cons a (Fin.cons b m)) =
      unitModel (I := I) (M := M) g (s' + 2) U x
        (Fin.cons a (Fin.cons (tangentLinearMapToModel (I := I) (Λ x) b) m)) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SSpace (s' + 2) I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
        (slotExtend (I := I) (M := M) g (s' + 1) (s' + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ)).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
          U.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace (s' + 2) I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
        (slotExtend (I := I) (M := M) g (s' + 1) (s' + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ)).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
          U.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [slotExtend_toSection]
  rw [slotExtendFib_apply_eval (I := I) (M := M) (s' + 1) (s' + 1) x _ _
    a (Fin.cons b m)]
  rw [show (show Tensor0SSpace (s' + 1) I x →L[ℝ] Tensor0SSpace (s' + 1) I x from
      (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ).toSection x) =
      slotInsertEndoFib (I := I) (M := M) (s' + 1) 0 x (Λ x) from
    slotInsertEndoCc_toSection (I := I) (M := M) g s' Λ x]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (s' + 1) 0 x (Λ x)]
  unfold unitModel
  rw [← TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
      U.toSection x) (unitTensor (I := I) (M := M) x))
    (v0 := a)
    (vs := Fin.cons (tangentLinearMapToModel (I := I) (Λ x) b) m)]
  congr 1
  rw [show (Fin.cons b m : Fin (s' + 1) → E) 0 = b from rfl]
  exact Fin.update_cons_zero _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotExtend_slotInsertEndoCc_cons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotExtend_slotInsertEndoCc_cons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotExtend_slotInsertEndoCc_cons ``Submission.DifferentialGeometry.Analysis.Sobolev.unitModel_operatorFieldApplication_slotExtend_slotInsertEndoCc_cons

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem operatorFieldApplication_slotExtend_slotInsert_homTensorRSFieldApply_swap_conj
    (g : SmoothRiemannianMetric I M) (s' : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (F : HomTensorRSField (E := E) (M := M) 0 (s' + 2) (s' + 2) I)
    (hF : ∀ (x : M) (T : TensorRSSpace 0 (s' + 2) I x) (D : Tensor0SSpace 0 I x)
      (a b : TangentSpace I x) (m : Fin s' → TangentSpace I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from
            (show TensorRSSpace 0 (s' + 2) I x →L[ℝ] TensorRSSpace 0 (s' + 2) I x from F x) T) D)
          (Fin.cons a (Fin.cons b m)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s' + 2) I x from T) D)
          (Fin.cons b (Fin.cons a m)))
    (U : SmoothCcTensor g 0 (s' + 2)) :
    operatorFieldApply (I := I) (M := M) g (s' + 2) (s' + 2)
        (slotExtend (I := I) (M := M) g (s' + 1) (s' + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g s' Λ))
        (homTensorRSFieldApply (I := I) (M := M) g 0 (s' + 2) (s' + 2) F U) =
      homTensorRSFieldApply (I := I) (M := M) g 0 (s' + 2) (s' + 2) F
        (operatorFieldApply (I := I) (M := M) g (s' + 2) (s' + 2)
          (endoSlotZeroCcTensor (I := I) (M := M) g (s' + 1) Λ) U) := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  rw [show w = Fin.cons (w 0) (Matrix.vecTail w) from (Fin.cons_self_tail w).symm]
  rw [show (Matrix.vecTail w) = Fin.cons (Matrix.vecTail w 0) (Matrix.vecTail (Matrix.vecTail w))
    from (Fin.cons_self_tail (Matrix.vecTail w)).symm]
  rw [unitModel_operatorFieldApplication_slotExtend_slotInsertEndoCc_cons (I := I) (M := M) g s' Λ
    (homTensorRSFieldApply (I := I) (M := M) g 0 (s' + 2) (s' + 2) F U) x
    (w 0) (Matrix.vecTail w 0) (Matrix.vecTail (Matrix.vecTail w))]
  rw [show unitModel (I := I) (M := M) g (s' + 2)
      (homTensorRSFieldApply (I := I) (M := M) g 0 (s' + 2) (s' + 2) F U) x
      (Fin.cons (w 0)
        (Fin.cons (tangentLinearMapToModel (I := I) (Λ x) (Matrix.vecTail w 0))
          (Matrix.vecTail (Matrix.vecTail w)))) =
      unitModel (I := I) (M := M) g (s' + 2) U x
        (Fin.cons (tangentLinearMapToModel (I := I) (Λ x) (Matrix.vecTail w 0))
          (Fin.cons (w 0) (Matrix.vecTail (Matrix.vecTail w)))) from by
    rw [unitModel_homTensorRSFieldApply_swap_eq_domDomCongr (I := I) (M := M) g s' F hF U x,
      ContinuousMultilinearMap.domDomCongr_apply,
      cons_cons_comp_swap01 (w 0)
        (tangentLinearMapToModel (I := I) (Λ x) (Matrix.vecTail w 0))
        (Matrix.vecTail (Matrix.vecTail w))]]
  rw [unitModel_homTensorRSFieldApply_swap_eq_domDomCongr (I := I) (M := M) g s' F hF
    (operatorFieldApply (I := I) (M := M) g (s' + 2) (s' + 2)
      (endoSlotZeroCcTensor (I := I) (M := M) g (s' + 1) Λ) U) x,
    ContinuousMultilinearMap.domDomCongr_apply,
    cons_cons_comp_swap01 (w 0) (Matrix.vecTail w 0)
      (Matrix.vecTail (Matrix.vecTail w))]
  rw [show (Fin.cons (Matrix.vecTail w 0)
      (Fin.cons (w 0) (Matrix.vecTail (Matrix.vecTail w))) : Fin (s' + 2) → E) =
      Fin.cons (Matrix.vecTail w 0)
        (Fin.cons (w 0) (Matrix.vecTail (Matrix.vecTail w))) from by
    congr 1]
  rw [unitModel_operatorFieldApplication_slotInsertEndoCc_cons (I := I) (M := M) g (s' + 1) Λ U x
    (Matrix.vecTail w 0)
    (Fin.cons (w 0) (Matrix.vecTail (Matrix.vecTail w)))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.operatorFieldApplication_slotExtend_slotInsert_homTensorRSFieldApply_swap_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.operatorFieldApplication_slotExtend_slotInsert_homTensorRSFieldApply_swap_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.operatorFieldApplication_slotExtend_slotInsert_homTensorRSFieldApply_swap_conj ``Submission.DifferentialGeometry.Analysis.Sobolev.operatorFieldApplication_slotExtend_slotInsert_homTensorRSFieldApply_swap_conj

end Sobolev
end Analysis
end DifferentialGeometry

end
