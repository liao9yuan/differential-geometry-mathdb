import Submission.DifferentialGeometry.Topology.Manifold.ClosedOriented
import Submission.DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Submission.DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }

universe u v

namespace ConnectedClosedOrientedManifold

variable (N : ConnectedClosedOrientedManifold.{v} 3) {X : Type u} [TopologicalSpace X] (h : X ≃ₜ N.Carrier)

private def pullbackSmoothOrientation :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
    Manifold.SmoothOrientation (𝓡 3) X := by
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  let _ : IsManifold (𝓡 3) ∞ X :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  let F := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) h
  let so := Manifold.smoothOrientationOfManifoldOrientation (𝓡 3)
    (OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr N.orientation.dimension_eq.symm) N.orientation)
  exact Manifold.pullbackSmoothOrientation (𝓡 3) (𝓡 3) F F.contMDiff
    (fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective) so

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackSmoothOrientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackSmoothOrientation target :: scope.openDecls } }

private def pullbackOrientation :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
    ManifoldOrientation (𝓡 3) X 3 := by
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  let _ : IsManifold (𝓡 3) ∞ X :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  let O := Classical.choose (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3)
    (pullbackSmoothOrientation N h))
  exact OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr (by simp : Module.finrank ℝ E3 = 3)) O

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientation target :: scope.openDecls } }

def pullback : ConnectedClosedOrientedManifold.{u} 3 where
  Carrier := X
  topology := inferInstance
  charts := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  smooth := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  hausdorff := h.symm.t2Space
  compact := h.symm.compactSpace
  connected := h.connectedSpace_iff.mpr inferInstance
  orientation := pullbackOrientation N h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullback ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullback

def pullbackOrientedDiffeomorph :
    ClosedOrientedManifold.OrientedDiffeomorph (pullback N h).toClosedOrientedManifold N.toClosedOrientedManifold := by
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  let _ : IsManifold (𝓡 3) ∞ X :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  let F := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) h
  refine ⟨F, ?_⟩
  let so := Manifold.smoothOrientationOfManifoldOrientation (𝓡 3)
    (OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr N.orientation.dimension_eq.symm) N.orientation)
  let hbij : ∀ x, _root_.Function.Bijective (mfderiv (𝓡 3) (𝓡 3) F x) :=
    fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective
  apply Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation F F.contMDiff hbij so
    (pullbackOrientation N h) N.orientation
  · intro y
    rfl
  · intro x
    change Orientation.reindex ℝ E3 _
      ((Classical.choose (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3)
        (pullbackSmoothOrientation N h))).orientation x) = _
    rw [Classical.choose_spec (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3)
      (pullbackSmoothOrientation N h))]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph

theorem pullbackOrientedDiffeomorph_apply (x : X) :
    (pullbackOrientedDiffeomorph N h).val x = h x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph_apply

end ConnectedClosedOrientedManifold
end DifferentialGeometry.Topology
