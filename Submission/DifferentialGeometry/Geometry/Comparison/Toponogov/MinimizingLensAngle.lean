import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteTriangleEquality
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Curvature.Nonnegative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem comparisonAngle_le_of_equal_radius_minimizing_lenses
    (g : SmoothRiemannianMetric I3 M) (hcomplete : RiemannianMetricComplete g)
    (hsec : HasNonnegativeSectionalCurvature g) (y p z q w : M) {r : ℝ}
    (hr : 0 < r) (hrp : r < metricDistance g y p) (hrz : r < metricDistance g y z)
    (hq : metricDistance g y q = r) (hw : metricDistance g y w = r)
    (hqp : metricDistance g q p = metricDistance g y p - r)
    (hwz : metricDistance g w z = metricDistance g y z - r) :
    comparisonAngle (metricDistance g y p) (metricDistance g y z) (metricDistance g p z) ≤
      comparisonAngle r r (metricDistance g q w) := by
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I3 M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : M => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I3) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hd (a b : M) : (_root_.Manifold.riemannianEDist I3 a b).toReal = metricDistance g a b := by
    rw [metricDistance, riemannianEDistOf_eq_riemannianEDist g hEnorm]
  obtain ⟨u, hu, huq⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm y q
    (by rw [hd, hq]; exact hr)
  rw [hd, hq] at huq
  obtain ⟨v, hv, hvw⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm y w
    (by rw [hd, hw]; exact hr)
  rw [hd, hw] at hvw
  have hup : intrinsicGeodesic g hEnorm y u (metricDistance g y p) = p := by
    have hh := intrinsicGeodesic_continues_of_distance_add g hEnorm y p u hu hr
      (sub_pos.mpr hrp) (by
        rw [add_sub_cancel, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) y p)])
      (by
        rw [huq, ← hqp, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) q p)])
    simpa only [add_sub_cancel] using hh
  have hvz : intrinsicGeodesic g hEnorm y v (metricDistance g y z) = z := by
    have hh := intrinsicGeodesic_continues_of_distance_add g hEnorm y z v hv hr
      (sub_pos.mpr hrz) (by
        rw [add_sub_cancel, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) y z)])
      (by
        rw [hvw, ← hwz, ← hd, ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I3) w z)])
    simpa only [add_sub_cancel] using hh
  have hh := complete_comparisonAngle_shortening g hEnorm hsec y u v
    r (metricDistance g y p) r (metricDistance g y z) hr hrp.le hr hrz.le hu hv
    (by rw [hup, hd]) (by rw [hvz, hd])
  simpa only [hup, hvz, huq, hvw, hd] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_le_of_equal_radius_minimizing_lenses then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_le_of_equal_radius_minimizing_lenses"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_le_of_equal_radius_minimizing_lenses ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonAngle_le_of_equal_radius_minimizing_lenses

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
