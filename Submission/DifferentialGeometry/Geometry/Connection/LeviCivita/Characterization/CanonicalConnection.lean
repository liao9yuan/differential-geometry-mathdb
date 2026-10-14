import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.Torsion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leviCivitaConnectionOfMetric_apply_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (leviCivitaConnectionOfMetric (I := I) g).toFun σ x v
      = (LeviCivita (I := I) g).toFun σ x v := by
  refine LeviCivita_unique g (leviCivitaConnectionOfMetric (I := I) g) ?_ ?_ hσ v
  · funext y
    exact (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g).2 y
  · exact leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_apply_eq_leviCivita then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_apply_eq_leviCivita"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_apply_eq_leviCivita ``Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_apply_eq_leviCivita

end Connection
end Geometry
end DifferentialGeometry
