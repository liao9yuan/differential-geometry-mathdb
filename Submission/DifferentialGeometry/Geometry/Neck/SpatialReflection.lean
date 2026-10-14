import Submission.DifferentialGeometry.Geometry.Neck.Spatial
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckAxialReflection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

def SpatialNeck.axialReflection (nk : SpatialNeck g eps p) : SpatialNeck g eps p := by
  have hU : ∀ y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹,
      cylinderAxialReflection y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ := by
    intro y hy
    simp only [cylinderAxialReflection_apply, _root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_Ioo]
    exact ⟨by linarith [hy.2.2], by linarith [hy.2.1]⟩
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := nk.Q_pos
    cylinder := nk.cylinder
    map := cylinderAxialReflection.trans nk.map
    center := nk.center
    center_eq := ?_
    domain := fun y hy => ⟨mem_univ _, nk.domain (hU y hy)⟩
    comparison := ?_ }
  · change nk.map (cylinderAxialReflection (nk.center, 0)) = p
    simpa only [cylinderAxialReflection_apply, neg_zero] using nk.center_eq
  · apply axialReflectionMetricComparison
      (fun s hs y v w => ?_) hU
      (fun y hy => nk.map.mdifferentiableAt (by simp) (nk.domain (hU y hy))) nk.comparison
    rw [cylinderAxialReflection_mfderiv, cylinderAxialReflection_mfderiv]
    exact CylinderReference.inner_axialReflection nk.cylinder le_rfl y v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection

@[simp] theorem SpatialNeck.axialReflection_apply
    (nk : SpatialNeck g eps p) (q : Sphere 2) (t : ℝ) :
    nk.axialReflection.map (q, t) = nk.map (q, -t) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.axialReflection_apply

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
