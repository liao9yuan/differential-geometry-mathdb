import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Commutation.ParallelNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SNabla
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tensorRSCovariantDerivative_zeroS_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_zeroS_unit_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_zeroS_unit_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_zeroS_unit_eval ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSCovariantDerivative_zeroS_unit_eval

noncomputable def unitScalarRSLift {s : ℕ} (x : M) (T : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  TensorRSSpace.ofCLM
    (ContinuousLinearMap.smulRight
      (tensor0Iso (I := I) M x).toContinuousLinearMap T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLift ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLift

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLift_apply {s : ℕ} (x : M) (T : Tensor0SSpace s I x)
    (D : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        unitScalarRSLift (I := I) (M := M) x T) D =
      (tensor0Iso (I := I) M x D) • T := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitScalarRSLift_apply_unit {s : ℕ} (x : M) (T : Tensor0SSpace s I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        unitScalarRSLift (I := I) (M := M) x T)
        (unitZeroSec (I := I) (M := M) x) = T := by
  rw [unitScalarRSLift_apply]
  have hscalar : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := scalarFn_unitZero (I := I) (M := M)
    have := congrFun h x
    simpa [scalarFn_apply, unitZeroSec_apply] using this
  rw [hscalar, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply_unit ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLift_apply_unit

noncomputable def unitScalarRSLiftSection {s : ℕ} (S : Π y : M, Tensor0SSpace s I y) :
    Π y : M, TensorRSSpace 0 s I y :=
  fun y => unitScalarRSLift (I := I) (M := M) y (S y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLiftSection_apply {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y) (y : M) :
    unitScalarRSLiftSection (I := I) (M := M) S y =
      unitScalarRSLift (I := I) (M := M) y (S y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitScalarRSLiftSection_apply_unit {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y) (y : M) :
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        unitScalarRSLiftSection (I := I) (M := M) S y)
        (unitZeroSec (I := I) (M := M) y) = S y := by
  rw [unitScalarRSLiftSection_apply, unitScalarRSLift_apply_unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_unit ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_unit

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitScalarRSLiftSection_apply_at_section {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y)
    (Y : Π y : M, Tensor0SSpace 0 I y) (y : M) :
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        unitScalarRSLiftSection (I := I) (M := M) S y) (Y y) =
      scalarFn (I := I) (M := M) Y y • S y := by
  rw [unitScalarRSLiftSection_apply, unitScalarRSLift_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_at_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_at_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_at_section ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLiftSection_apply_at_section

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem contMDiff_unitScalarRSLiftSection {s : ℕ}
    (S : Π y : M, Tensor0SSpace s I y)
    (hS : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (unitScalarRSLiftSection (I := I) (M := M) S y)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun y : M => Tensor0SSpace 0 I y)
    (V₂ := fun y : M => Tensor0SSpace s I y)
    (φ := fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
      unitScalarRSLiftSection (I := I) (M := M) S y))
  intro Y
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn (I := I) (M := M) (fun y => Y y)) :=
    (contMDiff_scalarFn_iff_section (I := I) (M := M) (fun y => Y y)).mpr Y.contMDiff
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (scalarFn (I := I) (M := M) (fun y => Y y) y • S y)) :=
    ContMDiff.smul_section hscalar hS
  have hpt : (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          unitScalarRSLiftSection (I := I) (M := M) S y) (Y y))) =
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (scalarFn (I := I) (M := M) (fun y => Y y) y • S y)) := by
    funext y
    rw [unitScalarRSLiftSection_apply_at_section (I := I) (M := M) S (fun y => Y y) y]
  rw [hpt]
  exact hsmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.contMDiff_unitScalarRSLiftSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.contMDiff_unitScalarRSLiftSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.contMDiff_unitScalarRSLiftSection ``Submission.DifferentialGeometry.Geometry.Connection.contMDiff_unitScalarRSLiftSection

noncomputable def unitScalarRSLiftCₛ {s : ℕ}
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
  ⟨fun y : M => unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) y,
   contMDiff_unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) S.contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] theorem unitScalarRSLiftCₛ_apply {s : ℕ}
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯) (y : M) :
    unitScalarRSLiftCₛ (I := I) (M := M) S y =
      unitScalarRSLiftSection (I := I) (M := M) (fun z => S z) y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ_apply ``Submission.DifferentialGeometry.Geometry.Connection.unitScalarRSLiftCₛ_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun y : M => Tensor0SSpace s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M => S y) x v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => unitScalarRSLiftCₛ (I := I) (M := M) S y) x v)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  rw [tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g s
    (unitScalarRSLiftCₛ (I := I) (M := M) S) x v]
  have hsec : (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          unitScalarRSLiftCₛ (I := I) (M := M) S y)
          (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M => S y) := by
    funext y
    rw [unitScalarRSLiftCₛ_apply]
    exact unitScalarRSLiftSection_apply_unit (I := I) (M := M) (fun z => S z) y
  rw [hsec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SCovariantDerivative_eq_tensorRSCovariantDerivative

end Connection
end Geometry
end DifferentialGeometry

end
