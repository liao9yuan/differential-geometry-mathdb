import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.Core
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.Nonautonomous.TameBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem clm0_ext {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 0 I x}
    (h : Tensor0SSpace.toModel
          (φ (unitZeroSec (I := I) (M := M) x)) (fun i => Fin.elim0 i) =
        Tensor0SSpace.toModel
          (ψ (unitZeroSec (I := I) (M := M) x)) (fun i => Fin.elim0 i)) :
    φ = ψ := by
  have hunit :
      φ (unitZeroSec (I := I) (M := M) x) =
        ψ (unitZeroSec (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro slots
    have hslots : slots = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    subst slots
    exact h
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D,
    map_smul, map_smul, hunit]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.clm0_ext
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.clm0_ext target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private theorem traceFib_diag
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g 0 x D)
        (fun i : Fin 0 => Fin.elim0 i) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.eval D
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  rw [cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 0 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel D) (fun i : Fin 0 => Fin.elim0 i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Tensor0SSpace.toModel_apply_tangent]
  congr 1
  funext a
  fin_cases a <;> rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.traceFib_diag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.traceFib_diag target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lapTrace_diag
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    scalarLapTraceAt (I := I) g D =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.eval D
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  let frame : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have horth : ∀ i j, g.inner x (frame i) (frame j) =
      if i = j then 1 else 0 := by
    intro i j
    simpa only [frame] using
      smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hli : LinearIndependent ℝ frame := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hp : g.inner x (∑ i, c i • frame i) (frame j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, sum_apply,
      Finset.sum_eq_single j] at hp
    · rw [ContinuousLinearMap.map_smul,
        smul_apply, horth j j,
        if_pos rfl, smul_eq_mul, mul_one] at hp
      exact hp
    · intro i _ hij
      rw [ContinuousLinearMap.map_smul,
        smul_apply, horth i j,
        if_neg (by simpa using hij), smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hli
      (by rw [Fintype.card_fin]; rfl)
  have hbasis (i) : basis i = frame i := by
    simp only [basis, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    intro i j
    constructor <;>
      simp [identityInvMetric, diagonalInvMetric, hbasis, horth]
  rw [scalarLapTraceAt,
    metricTracePair0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) hinv]
  simp only [hbasis, frame]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul]
    rw [← Tensor0SSpace.toModel_apply_tangent]
    rfl
  · intro j _ hji
    rw [identityInvMetric,
      diagonalInvMetric_eq_zero_of_ne (fun h => hji h.symm), _root_.MulZeroClass.zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.lapTrace_diag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.lapTrace_diag target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private theorem trace_eq_lap
    (a : SmoothRiemannianMetric I M) (x : M)
    (D Hs : Tensor0SSpace 2 I x)
    (hdiag : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.eval D
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) a x i x)
            (smoothOrthoFrame (I := I) a x i x)) =
        Tensor0SSpace.eval Hs
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) a x i x)
            (smoothOrthoFrame (I := I) a x i x))) :
    Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) a 0 x D)
        (fun i : Fin 0 => Fin.elim0 i) =
      scalarLapTraceAt (I := I) a Hs := by
  rw [traceFib_diag (I := I) (M := M),
    lapTrace_diag (I := I) (M := M)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hdiag i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.trace_eq_lap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.trace_eq_lap target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lift_unit {x : M} (c : ℝ) :
    Tensor0SSpace.toModel
        ((Tensor0SSpace.toRS0
            ((Tensor0SNabla.tensor0Iso I M x).symm c))
          (unitZeroSec (I := I) (M := M) x))
        (fun i : Fin 0 => Fin.elim0 i) = c := by
  rw [Tensor0SSpace.toRS0_apply]
  have hu : (tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) x)
      (unitZeroSec (I := I) (M := M) x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hu, one_smul]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm c) = c
  rw [ContinuousLinearEquiv.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.lift_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.lift_unit target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem one0_eq_unit (x : M) :
    Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) x =
      unitZeroSec (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro slots
  have hone : Tensor0SSpace.toModel
      (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) x) slots = (1 : ℝ) :=
    Tensor0SField.one0_apply (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) x slots
  have hunit : Tensor0SSpace.toModel
      (unitZeroSec (I := I) (M := M) x) slots = (1 : ℝ) := by
    calc
      _ = Tensor0SSpace.toModel
          (Tensor0SSpace.ofModel (I := I) (x := x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => E) (1 : ℝ))) slots :=
        congrArg
          (fun T : Tensor0SSpace 0 I x => Tensor0SSpace.toModel T slots)
          (unitZeroSec_apply (I := I) (M := M) x)
      _ = ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) (1 : ℝ) slots :=
        congrArg
          (fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ => f slots)
          (Tensor0SSpace.toModel_ofModel (I := I) (x := x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => E) (1 : ℝ)))
      _ = 1 := by
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  exact hone.trans hunit.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.one0_eq_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.one0_eq_unit target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem grad_cc_apply
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 0)
    (x : M) (X : TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          (iteratedCovGrad (I := I) (M := M) g 0 0 1 U).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun _ : Fin 1 => X) =
      mvfderiv (I := I)
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection) x X := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) U.toSection
  let A : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞ f hf
  have hunit (y : M) :
      (tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) y)
        (unitZeroSec (I := I) (M := M) y) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  have hsection :
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 0 I y from
          U.toSection y) (unitZeroSec (I := I) (M := M) y)) =
        fun y : M => A y := by
    funext y
    rw [← TensorRSField.lift_scalar0
      (n := (∞ : WithTop ℕ∞)) U.toSection,
      Tensor0SField.toRS0_apply, hunit, one_smul]
  have hscalar :
      Tensor0SNabla.scalarFn I M (fun y : M => A y) = f := by
    funext y
    rw [Tensor0SNabla.scalarFn_eq_apply_zero]
    change Tensor0SField.toScalarField ∞ A y = f y
    exact congrFun (Tensor0SField.toScalarField_fromScalarField ∞ f hf) y
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [covGrad_toSection_apply_natural (I := I) (M := M) g 0 0 U x
    (unitZeroSec (I := I) (M := M) x) (fun _ : Fin 1 => X)]
  rw [tensorCovDerivAt_def,
    tensorRSCovariantDerivative_zeroS_unit_eval, hsection,
    Tensor0SNabla.tensor0SCovariantDerivative_apply_zero, hscalar]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (mvfderiv (I := I) f x X)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.grad_cc_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.grad_cc_apply target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem grad2_cc_diag
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 0)
    (B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (iteratedCovGrad (I := I) (M := M) g 0 0 2 U).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (vec2 (I := I) (B x) (B x)) =
      Tensor0SSpace.eval (hessianSec (I := I) (LeviCivita (I := I) g)
        (by
          simpa [LeviCivita] using
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) g))
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection)
        (TensorRSField.scalar0_smooth
          (n := (∞ : WithTop ℕ∞)) U.toSection) x)
        (vec2 (I := I) (B x) (B x)) := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) U.toSection
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) g) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let m0 : Fin 0 → TangentSpace I x := fun i => Fin.elim0 i
  have hslots :
      Fin.cons (B x) (Fin.cons (B x) m0) = vec2 (I := I) (B x) (B x) := by
    funext i
    fin_cases i <;> rfl
  have hiter :
      iteratedCovGrad (I := I) (M := M) g 0 0 2 U =
        covGrad (I := I) (M := M) g 0 1
          (covGrad (I := I) (M := M) g 0 0 U) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hbridge :=
    tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval
      (I := I) (M := M) g 0 U
      (X := fun y => B y) (Y := fun y => B y)
      B.contMDiff B.contMDiff x m0
  rw [hiter, ← hslots, hbridge]
  have hrepr : (fun y : M => U.toSection y) =
      fun y : M =>
        (Tensor0SField.fromScalarField ∞ f hf).toTensorRSField ∞ y := by
    funext y
    exact congrArg (fun T => T y)
      (TensorRSField.lift_scalar0
        (n := (∞ : WithTop ℕ∞)) U.toSection).symm
  rw [hrepr]
  rw [tensorSecondCovDeriv_def,
    secondRS_scalar (I := I) (M := M) g hcov hf B x]
  rw [hslots, Tensor0SSpace.toRS0_apply]
  have hunit :
      (tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) x)
        (unitZeroSec (I := I) (M := M) x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hunit, one_smul]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (hessianSec (I := I) (LeviCivita (I := I) g) hcov f hf x
          (vec2 (I := I) (B x) (B x)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.grad2_cc_diag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.grad2_cc_diag target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem scalarLapDiff_eq
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) (x : M) :
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (scalarLapDiffCc (I := I) q h U).toSection x =
      ΔG (I := I) h ⟨_, (TensorRSField.scalar0_smooth
            (n := (∞ : WithTop ℕ∞)) U.toSection)⟩ x -
        ΔG (I := I) q ⟨_, (TensorRSField.scalar0_smooth
            (n := (∞ : WithTop ℕ∞)) U.toSection)⟩ x := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) U.toSection
  let hcovh : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) h) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) h)
  let hcovq : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) q) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) q)
  have hmch : IsMetricCompatible (I := I)
      (LeviCivita (I := I) h) h := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) h)
  have hmcq : IsMetricCompatible (I := I)
      (LeviCivita (I := I) q) q := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) q)
  let D2 : Tensor0SSpace 2 I x :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (iteratedCovGrad (I := I) (M := M) q 0 0 2 U).toSection x)
      (unitZeroSec (I := I) (M := M) x))
  let D1 : Tensor0SSpace 1 I x :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (iteratedCovGrad (I := I) (M := M) q 0 0 1 U).toSection x)
      (unitZeroSec (I := I) (M := M) x))
  let Hs : Tensor0SSpace 2 I x :=
    hessianSec (I := I) (LeviCivita (I := I) q) hcovq f hf x
  let CD : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connectionDifferenceFib (I := I) h q x) D1
  let Correction : Tensor0SSpace 2 I x :=
    connectionDifferenceOutput (I := I)
      (CovariantDerivative.difference
        (LeviCivita (I := I) h) (LeviCivita (I := I) q) x)
      (duSec (I := I) f hf x)
  have hsecond (a : SmoothRiemannianMetric I M) :
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) a 0 x D2)
          (fun i : Fin 0 => Fin.elim0 i) =
        scalarLapTraceAt (I := I) a Hs := by
    apply trace_eq_lap (I := I) (M := M)
    intro i
    convert grad2_cc_diag (I := I) (M := M) q U
      ⟨smoothOrthoFrame (I := I) a x i,
        smoothOrthoFrame_smooth (I := I) a x i⟩ x using 1 <;>
      rfl
  have hconn :
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x CD)
          (fun i : Fin 0 => Fin.elim0 i) =
        scalarLapTraceAt (I := I) h Correction := by
    apply trace_eq_lap (I := I) (M := M)
    intro i
    dsimp only [CD, D1, Correction]
    change Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connectionDifferenceFib (I := I) h q x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
            (iteratedCovGrad (I := I) (M := M) q 0 0 1 U).toSection x)
          (unitZeroSec (I := I) (M := M) x)))
        (vec2 (I := I)
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x)) =
        Tensor0SSpace.eval (connectionDifferenceOutput (I := I)
          (CovariantDerivative.difference
            (LeviCivita (I := I) h) (LeviCivita (I := I) q) x)
          (duSec (I := I) f hf x))
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) h x i x)
            (smoothOrthoFrame (I := I) h x i x))
    conv_lhs => rw [Tensor0SSpace.eval_eq]
    rw [connectionDifferenceFib_apply_eval]
    rw [show vec2 (I := I)
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x) 0 =
        smoothOrthoFrame (I := I) h x i x by simp only [vec2, ite_self],
      show vec2 (I := I)
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x) 1 =
        smoothOrthoFrame (I := I) h x i x by simp only [vec2, ite_self]]
    change Tensor0SSpace.eval D1
        (fun _ : Fin 1 => connectionDifference (I := I) h q x
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x)) = _
    rw [grad_cc_apply (I := I) (M := M) q U x
      (connectionDifference (I := I) h q x
        (smoothOrthoFrame (I := I) h x i x)
        (smoothOrthoFrame (I := I) h x i x))]
    rw [← connectionDifference_eq_difference (I := I) q h]
    rw [connectionDifferenceOutput_apply]
    rw [duSec_apply]
    conv_rhs => rw [Tensor0SSpace.eval_eq]
    rw [differential1FormFun_apply_eq_mvfderiv]
    congr 2
  rw [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, one0_eq_unit (I := I) (M := M)]
  rw [scalarLapDiff_apply (I := I) (M := M) q h U x,
    hsecond h, hsecond q, hconn]
  have hlap := lap_sub_conn (I := I) (M := M)
    (LeviCivita (I := I) h) (LeviCivita (I := I) q)
    hcovh hcovq h q hmch hmcq f hf x
  rw [laplacian_levi_eq (I := I) h hf x,
    laplacian_levi_eq (I := I) q hf x] at hlap
  simpa only [Hs, Correction, f, hf] using hlap.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarLapDiff_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarLapDiff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarLapDiff_eq ``Submission.DifferentialGeometry.Analysis.Spectral.scalarLapDiff_eq

private theorem lapDiff_unit
    (q h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) q) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 0 I x from
            (lapDiffSec (I := I) (M := M) q h v).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 0 I x from
            (scalarLapDiffCc (I := I) q h
              (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) := by
  rw [lapDiffSec_apply (I := I) (M := M) q h v x,
    lift_unit (I := I) (M := M)]
  have hvalue := scalarLapDiff_eq (I := I) (M := M) q h
    (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2) x
  rw [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, one0_eq_unit (I := I) (M := M)] at hvalue
  exact hvalue.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiff_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.lapDiff_unit target :: scope.openDecls } }

theorem lapDiffCore_eq_cc
    (q h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) q) :
    lapDiffCore (I := I) (M := M) q h v =
      SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0)
        (scalarLapDiffCc (I := I) q h
          (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)) := by
  change SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0)
      (lapDiffSec (I := I) (M := M) q h v) = _
  apply congrArg (fun W : SmoothCcTensor q 0 0 =>
    SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0) W)
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  exact clm0_ext (I := I) (M := M) (lapDiff_unit (I := I) (M := M) q h v x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffCore_eq_cc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffCore_eq_cc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffCore_eq_cc ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffCore_eq_cc

end DifferentialGeometry.Analysis.Spectral

end
