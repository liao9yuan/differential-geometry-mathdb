import Submission.DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Function
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

variable {E F H K X Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace K Y] [IsManifold J ∞ Y]
  [TopologicalSpace Z] [ChartedSpace H Z]

theorem isLocalDiffeomorphAt_pullback_of_comp (h : X ≃ₜ Y) (f : Z → X) (x : Z)
    (hf : IsLocalDiffeomorphAt I J ∞ (h ∘ f) x) :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := K) h
    IsLocalDiffeomorphAt I J ∞ f x := by
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := K) h
  let d := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := J) (n := ∞) h
  have hcomp := hf.comp (K := J) (P := X) (d.symm.isLocalDiffeomorph (h (f x)))
  have heq : d.symm ∘ (h ∘ f) = f := by funext y; exact h.symm_apply_apply _
  rwa [heq] at hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorphAt_pullback_of_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorphAt_pullback_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorphAt_pullback_of_comp ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorphAt_pullback_of_comp

theorem isLocalDiffeomorph_pullback_of_comp (h : X ≃ₜ Y) (f : Z → X)
    (hf : IsLocalDiffeomorph I J ∞ (h ∘ f)) :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := K) h
    IsLocalDiffeomorph I J ∞ f := fun x => isLocalDiffeomorphAt_pullback_of_comp h f x (hf x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isLocalDiffeomorph_pullback_of_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isLocalDiffeomorph_pullback_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isLocalDiffeomorph_pullback_of_comp ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_pullback_of_comp

end DifferentialGeometry.Topology
