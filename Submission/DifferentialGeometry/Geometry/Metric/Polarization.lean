import Submission.DifferentialGeometry.Geometry.Metric.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M']

theorem inner_eq_of_diag
    (g : SmoothRiemannianMetric I M) (g' : SmoothRiemannianMetric I' M')
    (x : M) (x' : M')
    (A : TangentSpace I x →L[ℝ] TangentSpace I' x')
    (hdiag : ∀ u, g'.inner x' (A u) (A u) = g.inner x u u)
    (u v : TangentSpace I x) :
    g'.inner x' (A u) (A v) = g.inner x u v := by
  have hleft :
      g'.inner x' (A (u + v)) (A (u + v)) =
        g'.inner x' (A u) (A u) +
          2 * g'.inner x' (A u) (A v) +
            g'.inner x' (A v) (A v) := by
    rw [map_add, map_add, map_add, add_apply,
      add_apply, g'.symm x' (A v) (A u)]
    ring
  have hright :
      g.inner x (u + v) (u + v) =
        g.inner x u u + 2 * g.inner x u v + g.inner x v v := by
    rw [(g.inner x).map_add u v, add_apply,
      (g.inner x u).map_add u v, (g.inner x v).map_add u v,
      g.symm x v u]
    ring
  have huv := hdiag (u + v)
  rw [hleft, hright, hdiag u, hdiag v] at huv
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.inner_eq_of_diag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.inner_eq_of_diag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.inner_eq_of_diag ``Submission.DifferentialGeometry.Geometry.Riemannian.inner_eq_of_diag

end Riemannian
end Geometry
end DifferentialGeometry
