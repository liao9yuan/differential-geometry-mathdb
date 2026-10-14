import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.ChartInvariance
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

def divergenceGWithBoundary
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => localDivergenceWithin (I := I) g x X x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergenceGWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergenceGWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergenceGWithBoundary ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergenceGWithBoundary

@[simp] lemma divergence_g_with_boundary_def
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceGWithBoundary (I := I) g X x =
      localDivergenceWithin (I := I) g x X x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_def

theorem voss_weyl_divergence_with_boundary_formula [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_α : x ∈ (chartAt H α).source) :
    divergenceGWithBoundary (I := I) g X x =
      localDivergenceWithin (I := I) g α X x := by
  unfold divergenceGWithBoundary
  exact localDivergenceWithin_chart_invariance
    (I := I) g x α X (mem_chart_source H x) hx_α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.voss_weyl_divergence_with_boundary_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.voss_weyl_divergence_with_boundary_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.voss_weyl_divergence_with_boundary_formula ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.voss_weyl_divergence_with_boundary_formula

theorem divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_int : x ∈ I.interior M) :
    divergenceGWithBoundary (I := I) g X x = divergenceG (I := I) g X x := by
  unfold divergenceGWithBoundary
  rw [divergence_g_def]
  exact localDivergenceWithin_eq_localDivergence_of_isInteriorPoint
    (I := I) g x X (mem_chart_source H x) hx_int

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint

theorem divergence_g_with_boundary_contMDiff [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(Real) ∞ (divergenceGWithBoundary g X) := by
  intro x
  have hx := (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have hlocal := (localDivergenceWithin_contMDiffOn g x X x (mem_chart_source H x)).contMDiffAt hx
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hx] with y hy
  exact voss_weyl_divergence_with_boundary_formula g x X hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiff ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiff


theorem divergence_g_with_boundary_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (divergenceGWithBoundary (I := I) g X)
      (I.interior M) :=
  (divergence_g_with_boundary_contMDiff g X).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiffOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiffOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiffOn_interior ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_contMDiffOn_interior


theorem divergence_g_with_boundary_continuousOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (divergenceGWithBoundary (I := I) g X) (I.interior M) :=
  (divergence_g_with_boundary_contMDiffOn_interior (I := I) g X).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_continuousOn_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_continuousOn_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_continuousOn_interior ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_continuousOn_interior

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
