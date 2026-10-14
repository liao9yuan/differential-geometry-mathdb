import Submission.DifferentialGeometry.Geometry.Operator.DivergenceNaturality
import Submission.DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem divergence_g_with_boundary_eq_divergence_metricCov [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceGWithBoundary g X x = divergence (metricCov g) X x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hleft := (divergence_g_with_boundary_contMDiff g X).continuous.continuousAt (x := x)
  have hright := (leviCivita_divergence_contMDiff g X).continuous.continuousAt (x := x)
  by_contra hne
  have hev := (hleft.sub hright).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨y, hy, hyint⟩ := mem_closure_iff_nhds.mp (I.dense_interior (M := M) x) _ hev
  apply hy
  apply sub_eq_zero.mpr
  exact (divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint g X hyint).trans
    (divergence_g_eq_leviCivita_divergence_of_isInteriorPoint g X hyint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_metricCov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_metricCov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_metricCov ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_eq_divergence_metricCov

theorem divergence_g_with_boundary_pullbackCross [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceGWithBoundary (Diffeomorph.pullbackMetricCross g Φ) X x =
      divergenceGWithBoundary g (pushFwdSectionCross Φ X) (Φ x) := by
  rw [divergence_g_with_boundary_eq_divergence_metricCov, divergence_g_with_boundary_eq_divergence_metricCov]
  exact divergence_metricCov_pullbackCross g Φ X x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_pullbackCross ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_pullbackCross

theorem divergence_g_with_boundary_restrictOpen [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : U) :
    divergenceGWithBoundary (g.restrictOpen U) (restrictOpenTangentSection U X) x =
      divergenceGWithBoundary g X x.1 := by
  rw [divergence_g_with_boundary_eq_divergence_metricCov, divergence_g_with_boundary_eq_divergence_metricCov]
  exact divergence_metricCov_restrictOpen g U X x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_restrictOpen ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.divergence_g_with_boundary_restrictOpen


end

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
