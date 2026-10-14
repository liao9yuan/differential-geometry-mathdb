import Submission.DifferentialGeometry.Geometry.Neck.Spatial
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def SpatialNeck.mono {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {p : M} {e f : ℝ}
    (nk : SpatialNeck g e p) (hef : e ≤ f) (hf : f < 1 / 11) : SpatialNeck g f p where
  eps_pos := nk.eps_pos.trans_le hef
  eps_small := hf
  Q_pos := nk.Q_pos
  cylinder := nk.cylinder
  map := nk.map
  center := nk.center
  center_eq := nk.center_eq
  domain := by
    have hinv := inv_anti₀ nk.eps_pos hef
    exact fun y hy => nk.domain ⟨hy.1, (neg_le_neg hinv).trans_lt hy.2.1, hy.2.2.trans_le hinv⟩
  comparison := by
    have hinv := inv_anti₀ nk.eps_pos hef
    exact nk.comparison.mono
      (fun y hy => ⟨hy.1, (neg_le_neg hinv).trans_lt hy.2.1, hy.2.2.trans_le hinv⟩)
      (Nat.ceil_le_ceil hinv) hef

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.mono

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
