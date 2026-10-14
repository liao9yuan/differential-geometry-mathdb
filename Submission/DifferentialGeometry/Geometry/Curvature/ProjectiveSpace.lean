import Submission.DifferentialGeometry.Geometry.Metric.ProjectiveSpace
import Submission.DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Conditions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem roundProjectiveMetric_sec_value (x : RealProjectiveSpace E)
    (X Y : TangentSpace (𝓡 n) x) :
    metricRm04StandardAt (roundProjectiveMetric (E := E) (n := n)) x X Y Y X =
      (roundProjectiveMetric (E := E) (n := n)).inner x X X *
          (roundProjectiveMetric (E := E) (n := n)).inner x Y Y -
        (roundProjectiveMetric (E := E) (n := n)).inner x X Y *
          (roundProjectiveMetric (E := E) (n := n)).inner x X Y := by
  obtain ⟨y, rfl⟩ := realProjectiveSpaceQuotientMap_surjective x
  let f := realProjectiveSpaceQuotientMap (E := E)
  have hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f :=
    realProjectiveSpaceQuotientMap_isLocalDiffeomorph
  let L := hf.mfderivToContinuousLinearEquiv (by simp) y
  obtain ⟨V, hV⟩ := L.surjective X
  obtain ⟨W, hW⟩ := L.surjective Y
  have hV' : mfderiv (𝓡 n) (𝓡 n) f y V = X := hV
  have hW' : mfderiv (𝓡 n) (𝓡 n) f y W = Y := hW
  have hcurv := metricRm04StandardAt_localPullMetric
    (roundProjectiveMetric (E := E) (n := n)) f hf y V W W V
  have hinner (A B : TangentSpace (𝓡 n) y) := localPullMetric_inner
    (roundProjectiveMetric (E := E) (n := n)) f hf y A B
  rw [localPullMetric_roundProjectiveMetric, roundMetric_sec_value] at hcurv
  simp only [hV', hW'] at hcurv
  rw [localPullMetric_roundProjectiveMetric] at hinner
  rw [← hcurv, hinner V V, hinner W W, hinner V W, hV', hW']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundProjectiveMetric_sec_value then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundProjectiveMetric_sec_value"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundProjectiveMetric_sec_value ``Submission.DifferentialGeometry.Geometry.roundProjectiveMetric_sec_value

theorem constantPositiveSectionalCurvatureMetric_roundProjectiveMetric :
    constantPositiveSectionalCurvatureMetric (roundProjectiveMetric (E := E) (n := n)) :=
  ⟨1, one_pos, fun x X Y => by rw [one_mul]; exact roundProjectiveMetric_sec_value x X Y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.constantPositiveSectionalCurvatureMetric_roundProjectiveMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.constantPositiveSectionalCurvatureMetric_roundProjectiveMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.constantPositiveSectionalCurvatureMetric_roundProjectiveMetric ``Submission.DifferentialGeometry.Geometry.constantPositiveSectionalCurvatureMetric_roundProjectiveMetric

end DifferentialGeometry.Geometry
