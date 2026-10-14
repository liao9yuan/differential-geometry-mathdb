import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Torsion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma trivToE_basepoint (α : M) (v : TangentSpace I α) :
    trivToE (I := I) α α v =
      tangentSpaceModelContinuousLinearEquiv (I := I) α v := by
  rw [tangentSpaceModelContinuousLinearEquiv_apply]
  classical
  have hcore : trivToE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.trivToE_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.trivToE_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.trivToE_basepoint ``Submission.DifferentialGeometry.Geometry.Connection.trivToE_basepoint

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelCorrection_basepoint_apply
    (g : SmoothRiemannianMetric I M) (α : M) (Y : E) (w : TangentSpace I α) :
    christoffelCorrection (I := I) g α α Y w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
                (tangentSpaceModelContinuousLinearEquiv (I := I) α w)) i *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α α)) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k := by
  classical
  rw [christoffelCorrection_apply]
  rw [trivToE_basepoint (I := I) α w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_apply ``Submission.DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelCorrection_basepoint_symm
    (g : SmoothRiemannianMetric I M) (α : M) (Y w : TangentSpace I α) :
    christoffelCorrection (I := I) g α α
        (tangentSpaceModelContinuousLinearEquiv (I := I) α Y) w =
      christoffelCorrection (I := I) g α α
        (tangentSpaceModelContinuousLinearEquiv (I := I) α w) Y := by
  classical
  have hsym := christoffelCorrection_symm_cancel (I := I) g α α w Y
  rw [trivToE_basepoint (I := I) α Y, trivToE_basepoint (I := I) α w] at hsym
  exact hsym

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_symm ``Submission.DifferentialGeometry.Geometry.Connection.christoffelCorrection_basepoint_symm

end Connection
end Geometry
end DifferentialGeometry
