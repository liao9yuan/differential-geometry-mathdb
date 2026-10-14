import Submission.DifferentialGeometry.Geometry.Neck.Spatial
import Submission.DifferentialGeometry.Geometry.Neck.SpatialChart
import Submission.DifferentialGeometry.Topology.LocallyFinite.Superlevel
import Mathlib.Topology.Semicontinuity.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M}

theorem SpatialNeck.locallyFinite_of_scalar_tendsto_atTop
    {ι : Type*} {eps : ι → ℝ} {x : ι → M}
    (nk : ∀ i, SpatialNeck g (eps i) (x i))
    {eta : ℝ} (hsmall : eta < 1 / 4323) (heps : ∀ i, eps i ≤ eta)
    (hscalar : _root_.Filter.Tendsto (fun i => metricScalarAt g (x i)) _root_.Filter.cofinite _root_.Filter.atTop) :
    LocallyFinite (fun i => (nk i).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-(eps i)⁻¹) (eps i)⁻¹)) := by
  have hc : 0 < 1 - 4323 * eta := by linarith
  apply (metricScalar_smooth g).continuous.upperSemicontinuous.locallyFinite_of_tendsto_lower_bound
    (hscalar.const_mul_atTop hc)
  rintro i z ⟨p, hp, rfl⟩
  have hratio := (abs_le.mp ((nk i).abs_scalar_ratio_sub_one_le hp)).1
  have hlow : 1 - 4323 * eta ≤
      metricScalarAt g ((nk i).map p) / metricScalarAt g (x i) := by
    linarith [heps i]
  exact (le_div_iff₀ (nk i).Q_pos).mp hlow

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.locallyFinite_of_scalar_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.locallyFinite_of_scalar_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.locallyFinite_of_scalar_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.locallyFinite_of_scalar_tendsto_atTop

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
