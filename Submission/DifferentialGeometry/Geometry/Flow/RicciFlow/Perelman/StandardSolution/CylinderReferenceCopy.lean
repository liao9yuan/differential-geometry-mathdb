import Submission.DifferentialGeometry.Geometry.Metric.CompletenessPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import Submission.DifferentialGeometry.Geometry.Neck.NormalizedDatum
import Submission.DifferentialGeometry.Topology.StandardModel
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev C := Metric.sphere (0 : E3) 1 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.C
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.C target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def cylinderReferenceCopy : DifferentialGeometry.Geometry.Topology.StandardModelCopy IC C E3 :=
  DifferentialGeometry.Geometry.Topology.standardModelCopy (I := IC) (M := C)
    (ContinuousLinearEquiv.ofFinrankEq (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceCopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceCopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceCopy ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceCopy

def cylinderReferenceMetric : SmoothRiemannianMetric (𝓡 3) cylinderReferenceCopy.Q :=
  Diffeomorph.pullbackMetricCross (roundCylinderMetric (E := E3) (n := 2))
    cylinderReferenceCopy.equiv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric

theorem cylinderReferenceMetric_inner (q : cylinderReferenceCopy.Q)
    (v w : TangentSpace (𝓡 3) q) :
    cylinderReferenceMetric.inner q v w =
      (roundCylinderMetric (E := E3) (n := 2)).inner
        (cylinderReferenceCopy.equiv.symm q)
        (mfderiv (𝓡 3) IC cylinderReferenceCopy.equiv.symm q v)
        (mfderiv (𝓡 3) IC cylinderReferenceCopy.equiv.symm q w) :=
  Diffeomorph.pullbackMetricCross_inner _ _ q v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_inner

theorem pullback_cylinderReferenceMetric :
    Diffeomorph.pullbackMetricCross cylinderReferenceMetric cylinderReferenceCopy.equiv =
      roundCylinderMetric (E := E3) (n := 2) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  let e := cylinderReferenceCopy.equiv
  have hd := (e.toOpenPartialHomeomorph_mdifferentiable
    (by decide : (∞ : ℕ∞ω) ≠ 0)).symm_comp_deriv
      (show x ∈ e.toHomeomorph.toOpenPartialHomeomorph.source from _root_.Set.mem_univ x)
  have hv : mfderiv (𝓡 3) IC e.symm (e x) (mfderiv IC (𝓡 3) e x v) = v :=
    congrArg (fun D => D v) hd
  have hw : mfderiv (𝓡 3) IC e.symm (e x) (mfderiv IC (𝓡 3) e x w) = w :=
    congrArg (fun D => D w) hd
  change (Diffeomorph.pullbackMetricCross
    (Diffeomorph.pullbackMetricCross (roundCylinderMetric (E := E3) (n := 2)) e.symm)
      e).inner x v w = _
  rw [Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner,
    hv, hw, e.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pullback_cylinderReferenceMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pullback_cylinderReferenceMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pullback_cylinderReferenceMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.pullback_cylinderReferenceMetric

theorem cylinderReferenceMetric_edist (q r : cylinderReferenceCopy.Q) :
    riemannianEDistOf cylinderReferenceMetric q r =
      riemannianEDistOf (roundCylinderMetric (E := E3) (n := 2))
        (cylinderReferenceCopy.equiv.symm q) (cylinderReferenceCopy.equiv.symm r) :=
  edistOf_pullbackMetricCross _ _ q r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist

theorem cylinderReferenceMetric_edist_equiv (x y : C) :
    riemannianEDistOf cylinderReferenceMetric
      (cylinderReferenceCopy.equiv x) (cylinderReferenceCopy.equiv y) =
        riemannianEDistOf (roundCylinderMetric (E := E3) (n := 2)) x y := by
  simpa only [Diffeomorph.symm_apply_apply] using
    cylinderReferenceMetric_edist (cylinderReferenceCopy.equiv x) (cylinderReferenceCopy.equiv y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist_equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist_equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist_equiv ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceMetric_edist_equiv

def cylinderPointedReference : PointedRiemannianManifold (𝓡 3) where
  M := cylinderReferenceCopy.Q
  basepoint := cylinderReferenceCopy.equiv (spherePoint, 0)
  metric := cylinderReferenceMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference

theorem cylinderPointedReference_complete : MetricComplete cylinderPointedReference := by
  have h0 : RiemannianMetricComplete (roundCylinderMetric (E := E3) (n := 2)) := by
    simpa only [shrinkingCylinderMetric_zero] using
      (shrinkingCylinderMetric_complete (E := E3) 0)
  have hQ : RiemannianMetricComplete cylinderReferenceMetric :=
    DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      h0 cylinderReferenceCopy.equiv.symm
  exact hQ.complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderPointedReference_complete

end DifferentialGeometry.PDE.RicciFlow

end
