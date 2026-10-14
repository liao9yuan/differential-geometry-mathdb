import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticReducedVolumeCovering
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientSphericalCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryCylinderMass

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (b : ℝ) (hb : b < 0) (p : F.M)
    (hmass : (1 / 2 : ℝ≥0∞) < asymptoticReducedVolume F.S b p) :
    Nonempty (DifferentialGeometry.Topology.SphereThree ≃ₘ⟮(𝓡 3), I3⟯ F.M) := by
  let : ConnectedSpace F.M := hF.connected
  obtain ⟨⟨q, hq, hsurj, hd⟩, _⟩ := exists_spherical_cover_of_compact_ancientKappa F hF
  obtain ⟨x, hx⟩ := hsurj p
  have hinj : Function.Injective q :=
    covering_injective_of_one_half_lt_asymptoticReducedVolume F.S F.isSolution q hd hq
      b (fun t ht => by simpa only [ancientTimeInterval_regular, Set.mem_Iio] using ht.trans_lt hb)
      (fun t ht y => ancientKappa_scalar_nonneg F hF (ht.trans hb.le) y) x
      (by simpa only [hx] using hmass)
  exact ⟨hd.diffeomorphOfBijective ⟨hinj, hsurj⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume

theorem nonempty_diffeomorph_sphere_of_compact_ordinary_cylinder
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (b : ℝ) (hb : b < 0) (p : F.M)
    (P : PointedRiemannianManifold (𝓡 3)) (g : SmoothRiemannianMetric (𝓡 3) P.M)
    (f : C^∞⟮(𝓡 3), P.M; ℝ⟯)
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, (𝓡 3)⟯ P.M)
    (hmetric : Diffeomorph.pullbackMetricCross g d = scalarOneShrinkingCylinderMetric 0 (by norm_num))
    (hpotential : ∀ z : SpatialNeckCylinder, f (d z) = 1 + z.2 ^ 2 / 4)
    (hmass : normalizedShrinkerMass g f = asymptoticReducedVolume F.S b p) :
    Nonempty (DifferentialGeometry.Topology.SphereThree ≃ₘ⟮(𝓡 3), I3⟯ F.M) := by
  exact nonempty_diffeomorph_sphere_of_one_half_lt_asymptoticReducedVolume F hF b hb p
    (one_half_lt_asymptoticReducedVolume_of_ordinary_cylinder F.S b p P g f d
      hmetric hpotential hmass)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_compact_ordinary_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_compact_ordinary_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_compact_ordinary_cylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_diffeomorph_sphere_of_compact_ordinary_cylinder

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
