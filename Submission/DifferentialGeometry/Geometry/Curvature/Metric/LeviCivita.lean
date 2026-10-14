import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.CanonicalConnection
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.RawFields
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Chart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_contMDiffCovariantDerivativeLocally (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally (LeviCivita (I := I) g) ∞ := by
  simpa [LeviCivita, metricCov] using (metricCov_smooth (I := I) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.leviCivita_contMDiffCovariantDerivativeLocally then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.leviCivita_contMDiffCovariantDerivativeLocally"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.leviCivita_contMDiffCovariantDerivativeLocally ``Submission.DifferentialGeometry.leviCivita_contMDiffCovariantDerivativeLocally

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    connectionRiemannCurvatureField (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        (fun p => X p) (fun p => Y p) (fun p => Z p) x
      = connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g)
        (fun p => X p) (fun p => Y p) (fun p => Z p) x := by
  simp [LeviCivita]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita ``Submission.DifferentialGeometry.connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem riemannCurvatureAt_lcOfMetric_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    riemannCurvatureAt (leviCivitaConnectionOfMetric (I := I) g)
        (metricCov_smooth (I := I) g) x
      = riemannCurvatureAt (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  classical
  have hcov₁ := metricCov_smooth (I := I) g
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  apply tensorRSSpace_ext (𝕜 := ℝ) 1 3 x
  intro α
  apply ContinuousMultilinearMap.ext
  intro v
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 0)
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 1)
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 2)
  have hv : v = vec3 (X x) (Y x) (Z x) := by
    funext i; fin_cases i <;> simp_all [vec3]
  rw [hv]
  change riemannCurvatureAt (leviCivitaConnectionOfMetric (I := I) g) hcov₁ x α
      (vec3 (X x) (Y x) (Z x)) =
    riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x α
      (vec3 (X x) (Y x) (Z x))
  rw [riemannCurvatureAt_apply_smooth (I := I) (leviCivitaConnectionOfMetric (I := I) g)
      hcov₁ X Y Z α,
    riemannCurvatureAt_apply_smooth (I := I) (LeviCivita (I := I) g) hcov₂ X Y Z α]
  exact congrArg _
    (connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita (I := I) g X Y Z x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannCurvatureAt_lcOfMetric_eq_leviCivita then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannCurvatureAt_lcOfMetric_eq_leviCivita"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannCurvatureAt_lcOfMetric_eq_leviCivita ``Submission.DifferentialGeometry.riemannCurvatureAt_lcOfMetric_eq_leviCivita

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connectionRiemannCurvatureField_tangentConst_eq_riemannOp
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y Z : TangentSpace I x) :
    connectionRiemannCurvatureField cov (CovariantDerivative.tangentConstAt (I := I) x X)
        (CovariantDerivative.tangentConstAt (I := I) x Y)
        (CovariantDerivative.tangentConstAt (I := I) x Z) x
      = riemannOp cov x X Y Z := by
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x X
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Y
  obtain ⟨Zc, hZc, hZcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Z
  rw [connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
      (I := I) cov hcov X Y Z Xc Yc Zc hXc hYc hZc]
  have hsec :
      connectionRiemannCurvatureField cov
          (fun p : M => Xc p) (fun p : M => Yc p) (fun p : M => Zc p) x
        = riemannSec cov (fun p : M => Xc p) (fun p : M => Yc p)
            (fun p : M => Zc p) x := rfl
  rw [hsec, ← riemannOp_apply_smooth (cov := cov) Xc.contMDiff Yc.contMDiff Zc.contMDiff,
    hXcx, hYcx, hZcx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.connectionRiemannCurvatureField_tangentConst_eq_riemannOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.connectionRiemannCurvatureField_tangentConst_eq_riemannOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.connectionRiemannCurvatureField_tangentConst_eq_riemannOp ``Submission.DifferentialGeometry.connectionRiemannCurvatureField_tangentConst_eq_riemannOp

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciCurvatureAt_leviCivita_apply_eq_ricciTensor
    (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciCurvatureAt (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x (vec2 v w)
      = ricciTensor (I := I) g x v w := by
  classical
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  rw [ricciCurvatureAt_eq_trace,
    ricciFromRm13At_apply_basis_trace (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x)
      (riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x) v w,
    ricciTensor_apply_basisSum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [riemannCurvatureAt_apply_const,
    connectionRiemannCurvatureField_tangentConst_eq_riemannOp (cov := LeviCivita (I := I) g) (hcov := hcov₂),
    cotangentToDual_dualToCotangent, Module.Basis.coord_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ricciCurvatureAt_leviCivita_apply_eq_ricciTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ricciCurvatureAt_leviCivita_apply_eq_ricciTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ricciCurvatureAt_leviCivita_apply_eq_ricciTensor ``Submission.DifferentialGeometry.ricciCurvatureAt_leviCivita_apply_eq_ricciTensor

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricRicciAt_apply_eq_ricciTensor
    (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 v w) = ricciTensor (I := I) g x v w := by
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  have key : riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
           = riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x :=
    riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x
  rw [metricRicciAt, ricciCurvatureAt_eq_trace, key, ← ricciCurvatureAt_eq_trace]
  exact ricciCurvatureAt_leviCivita_apply_eq_ricciTensor (I := I) g x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor ``Submission.DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricScalarAt_eq_zero_of_ricciTensor_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hRic : ∀ v w : TangentSpace I x, ricciTensor (I := I) g x v w = 0) :
    metricScalarAt (I := I) g x = 0 := by
  have hRicci : metricRicciAt (I := I) g x = 0 := by
    apply Tensor0SBundle.ext0S_basis (centeredChartTangentBasis (I := I) x)
    intro slots
    simp only [Tensor0SBundle.component0S_apply]
    change metricRicciAt (I := I) g x
      (fun a : Fin 2 => centeredChartTangentBasis (I := I) x (slots a)) = 0
    have hslots :
        (fun a : Fin 2 => centeredChartTangentBasis (I := I) x (slots a)) =
          vec2 (I := I)
            (centeredChartTangentBasis (I := I) x (slots 0))
            (centeredChartTangentBasis (I := I) x (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [hslots, metricRicciAt_apply_eq_ricciTensor]
    exact hRic _ _
  rw [metricScalarAt_def, hRicci]
  rw [show (0 : Tensor0SBundle.Tensor0SSpace 2 I x) =
      (0 : Real) • Geometry.Operator.metricTensor0S (I := I) g x by simp,
    Geometry.Operator.metricTracePair0SAt_smul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricScalarAt_eq_zero_of_ricciTensor_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricScalarAt_eq_zero_of_ricciTensor_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricScalarAt_eq_zero_of_ricciTensor_eq_zero ``Submission.DifferentialGeometry.metricScalarAt_eq_zero_of_ricciTensor_eq_zero

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricRm13At_eq_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm13At (I := I) g x
      = riemannCurvatureAt (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  change riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
     = riemannCurvatureAt (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x
  exact riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricRm13At_eq_riemannCurvatureAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricRm13At_eq_riemannCurvatureAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricRm13At_eq_riemannCurvatureAt ``Submission.DifferentialGeometry.metricRm13At_eq_riemannCurvatureAt

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem metricRm04At_eq_riemannCurvature04At
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) g x
      = riemannCurvature04At (I := I) g (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  have key : riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
           = riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x :=
    riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x
  change riemannCurvature04At (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
     = riemannCurvature04At (I := I) g (LeviCivita (I := I) g) hcov₂ x
  unfold riemannCurvature04At
  rw [key]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricRm04At_eq_riemannCurvature04At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricRm04At_eq_riemannCurvature04At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricRm04At_eq_riemannCurvature04At ``Submission.DifferentialGeometry.metricRm04At_eq_riemannCurvature04At

end DifferentialGeometry
