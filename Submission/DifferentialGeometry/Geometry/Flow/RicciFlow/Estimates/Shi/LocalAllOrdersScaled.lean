import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrders
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.IntervalTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators _root_.Bundle _root_.Submission.Bundle _root_.Topology



section MetricRescaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem closedBall_scaleMetric_eq
    (g : SmoothRiemannianMetric I M) (c : Real) (hc : 0 < c) (p : M) (R : Real) :
    {y : M | riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) p y ≤
        ENNReal.ofReal (Real.sqrt c * R)} =
      {y : M | riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R} := by
  have hne : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc))
  refine Set.ext fun y => ?_
  change riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) p y ≤
      ENNReal.ofReal (Real.sqrt c * R) ↔
    riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal R
  rw [edistOf_scale (I := I) c hc g p y,
    ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.closedBall_scaleMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.closedBall_scaleMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.closedBall_scaleMetric_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.closedBall_scaleMetric_eq

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
  [SigmaCompactSpace M] [T2Space M] in
theorem isCompact_closedBall_scaleMetric
    {g : SmoothRiemannianMetric I M} (c : Real) (hc : 0 < c) (p : M) (R : Real)
    (hball : IsCompact {y : M | riemannianEDistOf (I := I) g p y ≤
      ENNReal.ofReal R}) :
    IsCompact {y : M | riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) p y ≤
      ENNReal.ofReal (Real.sqrt c * R)} := by
  rw [closedBall_scaleMetric_eq (I := I) g c hc p R]
  exact hball

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isCompact_closedBall_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isCompact_closedBall_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isCompact_closedBall_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.isCompact_closedBall_scaleMetric

omit [SigmaCompactSpace M] in
theorem metricRm04_scaleMetric_smul
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04 (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • metricRm04 (I := I) (M := M) g x :=
  parabolicSolution_rm04 (I := I) (M := M)
    (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ 0)
    (⟨⟨fun _ => g⟩⟩ :
      SolutionOn (I := I) (M := M)
        (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ 0))
    0 c hc (Set.mem_univ 0) 0 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricRm04_scaleMetric_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricRm04_scaleMetric_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricRm04_scaleMetric_smul ``Submission.DifferentialGeometry.PDE.RicciFlow.metricRm04_scaleMetric_smul

omit [SigmaCompactSpace M] in
theorem metricRm04StandardAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (I := I) (M := M) (scaleMetric (I := I) c hc g) x X Y Z W =
      c * metricRm04StandardAt (I := I) (M := M) g x X Y Z W := by
  have h : metricRm04At (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • metricRm04At (I := I) (M := M) g x := by
    simpa using metricRm04_scaleMetric_smul (I := I) c hc g x
  simp [metricRm04StandardAt_apply, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricRm04StandardAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricRm04StandardAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricRm04StandardAt_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.metricRm04StandardAt_scaleMetric

omit [SigmaCompactSpace M] in
theorem sectionalBoundedBelowAt_scaleMetric
    {g : SmoothRiemannianMetric I M} {Ksec : Real} {x : M}
    (hsec : Geometry.Riemannian.SectionalBoundedBelowAt (I := I) g x Ksec)
    (c : Real) (hc : 0 < c) :
    Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
      (scaleMetric (I := I) c hc g) x (Ksec / c) := by
  intro v w
  have h := hsec v w
  have hcne : c ≠ 0 := ne_of_gt hc
  simp only [scaleMetric_inner, metricRm04StandardAt_scaleMetric (I := I) c hc g x v w w v]
  have hLHS :
      Ksec / c * (c * g.inner x v v * (c * g.inner x w w) - (c * g.inner x v w) ^ 2) =
        c * (Ksec * (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) := by
    field_simp
  rw [hLHS]
  exact mul_le_mul_of_nonneg_left h hc.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric

end MetricRescaling



section CurvatureScale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem nablaKRm04Field_cast
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    nablaKRm04Field (I := I) (S.cast D') t k = nablaKRm04Field (I := I) S t k := by
  induction k with
  | zero => simp only [nablaKRm04Field_zero, SolutionOn.cast_base]
  | succ k ih =>
      simp only [nablaKRm04Field_succ, ih, SolutionOn.cast_family_connection]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_cast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_cast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_cast ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04Field_cast

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem nablaKRm04NormSqIntrinsic_cast
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (S.cast D') k t x =
      nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_cast (I := I) S t k,
    SolutionOn.cast_metric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_cast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_cast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_cast ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_cast

def curvatureScaleSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier) :
    SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        (K * alpha) (K * omega) (mul_lt_mul_of_pos_left halphaomega hK)) :=
  (parabolicSolution (I := I) S 0 K hK h0).cast _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M]
    [T2Space M] [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
@[simp] theorem curvatureScaleSolution_metric
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier) (s : Real) :
    (curvatureScaleSolution (I := I) S hK h0).base.metric s =
      scaleMetric (I := I) K hK (S.base.metric (parabolicTime 0 K s)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
    [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [SigmaCompactSpace M]
    [T2Space M] [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem curvatureScaleSolution_metric_zero
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier) :
    (curvatureScaleSolution (I := I) S hK h0).base.metric 0 =
      scaleMetric (I := I) K hK (S.base.metric 0) := by
  rw [curvatureScaleSolution_metric, parabolicTime_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureScaleSolution_metric_zero

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem nablaKRm04NormSqIntrinsic_curvatureScaleSolution_eq_paraSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier) (k : ℕ) (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (curvatureScaleSolution (I := I) S hK h0) k s x =
      nablaKRm04NormSqIntrinsic (I := I) (parabolicSolution (I := I) S 0 K hK h0) k s x := by
  unfold curvatureScaleSolution
  exact nablaKRm04NormSqIntrinsic_cast (I := I) (parabolicSolution (I := I) S 0 K hK h0) k s x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution_eq_paraSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution_eq_paraSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution_eq_paraSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution_eq_paraSolution

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [SigmaCompactSpace M]
    [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem nablaKRm04NormSqIntrinsic_curvatureScaleSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier) (k : ℕ) (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (curvatureScaleSolution (I := I) S hK h0) k s x =
      (K⁻¹) ^ (2 + k) * nablaKRm04NormSqIntrinsic (I := I) S k (s / K) x := by
  have h := parabolicNablaKRmNormSq (I := I) S 0 K hK h0 k s x
  have hpt : parabolicTime 0 K s = s / K := by
    unfold parabolicTime
    ring
  rw [hpt] at h
  rw [nablaKRm04NormSqIntrinsic_curvatureScaleSolution_eq_paraSolution (I := I) S hK h0 k s x]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaKRm04NormSqIntrinsic_curvatureScaleSolution

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 2 M]
    [SigmaCompactSpace M] [BoundarylessManifold I M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem isSolutionOn_curvatureScaleSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {K : Real} (hK : 0 < K)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier) :
    IsSolutionOn (I := I) (curvatureScaleSolution (I := I) S hK h0) := by
  refine isSolutionOn_cast (I := I) (parabolicSolution_isSolutionOn (I := I) S hS 0 K hK h0) ?_ ?_
  · rw [parabolicInterval_closedOpen_carrier_eq halphaomega hK h0]
    simp only [sub_zero]
    rfl
  · rw [parabolicInterval_closedOpen_regular_eq halphaomega hK h0]
    simp only [sub_zero]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_curvatureScaleSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_curvatureScaleSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_curvatureScaleSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_curvatureScaleSolution

end CurvatureScale



section Corollary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

theorem shi_local_all_orders_curvature_scale_explicit_of_laplacianInput
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T K R Ksec Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hK : 0 < K) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I) (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I)
        (curvatureScaleSolution (I := I) S hK h0) (K * T) p
        {y : M | riemannianEDistOf (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
            ENNReal.ofReal R}
        r (Ksec / K) Clap Cconn
        (nablaRmSupWeight (I := I) (curvatureScaleSolution (I := I) S hK h0))) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
          ENNReal.ofReal (R / (2 * Real.sqrt K)) →
        Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalAllOrdersConst (Module.finrank Real E) m (K * T) R Clap Cconn * K ∧
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
            shiLocalAllOrdersConst (Module.finrank Real E) m (K * T) R Clap Cconn * K /
              Real.sqrt t ^ m := by
  intro m
  have hKne : K ≠ 0 := ne_of_gt hK
  have hsk : (0 : Real) < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hradius : Real.sqrt K * (R / Real.sqrt K) = R := by
    field_simp
  have hmet0 : (curvatureScaleSolution (I := I) S hK h0).base.metric 0 =
      scaleMetric (I := I) K hK (S.base.metric 0) :=
    curvatureScaleSolution_metric_zero (I := I) S hK h0
  have hballEq : {y : M |
      riemannianEDistOf (I := I)
        ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
          ENNReal.ofReal R} =
      {y : M | riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)} := by
    have h := closedBall_scaleMetric_eq (I := I) (S.base.metric 0) K hK p
      (R / Real.sqrt K)
    rw [hradius] at h
    rw [hmet0]
    exact h
  have hball' : IsCompact {y : M |
      riemannianEDistOf (I := I)
        ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
          ENNReal.ofReal R} := by
    rw [hballEq]
    exact hball
  have hsec' : ∀ y : M,
      riemannianEDistOf (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
            ENNReal.ofReal R →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) y (Ksec / K) := by
    intro y hy
    have hmem : y ∈ {z : M | riemannianEDistOf (I := I)
        ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p z ≤
          ENNReal.ofReal R} := hy
    rw [hballEq] at hmem
    have hy' : riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K) := hmem
    rw [hmet0]
    exact sectionalBoundedBelowAt_scaleMetric (I := I) (hsec y hy') K hK
  have hKsec' : Ksec / K ≤ 0 := by
    have hKinv : (0 : Real) ≤ K⁻¹ := (inv_pos.mpr hK).le
    have hprod := mul_nonneg (neg_nonneg.mpr hKsec) hKinv
    rw [div_eq_mul_inv]
    nlinarith [hprod]
  have halpha' : K * alpha < 0 := mul_neg_of_pos_of_neg hK halpha
  have hT' : (0 : Real) < K * T := mul_pos hK hT
  have hTomega' : K * T < K * omega := mul_lt_mul_of_pos_left hTomega hK
  have hu' : ∀ s ∈ Set.Icc (0 : Real) (K * T), ∀ y : M,
      riemannianEDistOf (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
            ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic (I := I) (curvatureScaleSolution (I := I) S hK h0) 0 s y
          ≤ 1 := by
    intro s hs y hy
    have hmemy : y ∈ {z : M | riemannianEDistOf (I := I)
        ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p z ≤
          ENNReal.ofReal R} := hy
    rw [hballEq] at hmemy
    have hy' : riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K) := hmemy
    rw [nablaKRm04NormSqIntrinsic_curvatureScaleSolution (I := I) S hK h0 0 s y]
    have hsK : s / K ∈ Set.Icc (0 : Real) T := by
      refine ⟨div_nonneg hs.1 hK.le, ?_⟩
      rw [div_le_iff₀ hK]
      calc s ≤ K * T := hs.2
        _ = T * K := by ring
    have hb := hu (s / K) hsK y hy'
    have hpow : (0 : Real) ≤ (K⁻¹) ^ (2 + 0) := by positivity
    calc (K⁻¹) ^ (2 + 0) * nablaKRm04NormSqIntrinsic (I := I) S 0 (s / K) y
        ≤ (K⁻¹) ^ (2 + 0) * K ^ 2 := mul_le_mul_of_nonneg_left hb hpow
      _ = 1 := by
          have h2 : (K⁻¹ : Real) ^ (2 + 0) = (K⁻¹ : Real) ^ 2 := by norm_num
          rw [h2, ← mul_pow, inv_mul_cancel₀ hKne, one_pow]
  have hC :=
    shi_local_all_orders_norm_explicit_of_laplacianInput (I := I)
      (curvatureScaleSolution (I := I) S hK h0)
      (isSolutionOn_curvatureScaleSolution (I := I) S hS hK h0) p halpha' hT' hTomega' hR
      hball' hKsec' hsec' hu' hClap hCconn hlap m
  set C : Real := shiLocalAllOrdersConst (Module.finrank Real E) m (K * T) R Clap Cconn
    with hCdef
  have hnorm : ∀ s ∈ Set.Ioc (0 : Real) (K * T), ∀ x : M,
      riemannianEDistOf (I := I)
          ((parabolicSolution (I := I) S 0 K hK h0).base.metric 0) p x ≤
            ENNReal.ofReal (R / 2) →
        Real.sqrt (s ^ m * nablaKRm04NormSqIntrinsic (I := I)
          (parabolicSolution (I := I) S 0 K hK h0) m s x) ≤ C := by
    intro s hs x hball
    have hb := (hC s hs x hball).1
    rwa [nablaKRm04NormSqIntrinsic_curvatureScaleSolution_eq_paraSolution
      (I := I) S hK h0 m s x] at hb
  have hmain :=
    shi_local_all_orders_unnormalized_of_normalized (I := I) S (m := m) p hK h0 hnorm
  intro t ht x hball
  have h1 := hmain t ht x hball
  refine ⟨h1, ?_⟩
  have hspos : (0 : Real) < Real.sqrt t ^ m := pow_pos (Real.sqrt_pos.mpr ht.1) m
  rw [le_div_iff₀ hspos]
  have hsplit : Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) =
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) * Real.sqrt t ^ m := by
    rw [Real.sqrt_mul (pow_nonneg ht.1.le m), sqrt_pow_of_nonneg ht.1.le, mul_comm]
  rw [← hsplit]
  exact h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_explicit_of_laplacianInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_explicit_of_laplacianInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_explicit_of_laplacianInput ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_explicit_of_laplacianInput

theorem shi_local_all_orders_curvature_scale_of_laplacianInput
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega))
    (hS : IsSolutionOn (I := I) S)
    {T K R Ksec Clap Cconn : Real} (p : M)
    (halpha : alpha < 0) (hK : 0 < K) (hT : 0 < T) (hTomega : T < omega) (hR : 0 < R)
    (h0 : (0 : Real) ∈
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega
        halphaomega).carrier)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        Geometry.Riemannian.SectionalBoundedBelowAt (I := I) (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric 0) p y ≤
          ENNReal.ofReal (R / Real.sqrt K) →
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : ∀ r ∈ Set.Ioc (R / 2) R,
      InitialDistanceFlowLaplacianBound (I := I)
        (curvatureScaleSolution (I := I) S hK h0) (K * T) p
        {y : M | riemannianEDistOf (I := I)
          ((curvatureScaleSolution (I := I) S hK h0).base.metric 0) p y ≤
            ENNReal.ofReal R}
        r (Ksec / K) Clap Cconn
        (nablaRmSupWeight (I := I) (curvatureScaleSolution (I := I) S hK h0))) :
    ∀ m : ℕ, ∃ C : Real, 0 ≤ C ∧
      ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
        riemannianEDistOf (I := I) (S.base.metric 0) p x ≤
            ENNReal.ofReal (R / (2 * Real.sqrt K)) →
          Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C * K ∧
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
              C * K / Real.sqrt t ^ m := fun m =>
  ⟨shiLocalAllOrdersConst (Module.finrank Real E) m (K * T) R Clap Cconn,
    shiLocalAllOrdersConst_nonneg _ _ _ _ _ _,
    shi_local_all_orders_curvature_scale_explicit_of_laplacianInput (I := I) S hS p halpha
      hK hT hTomega hR h0 hball hKsec hsec hu hClap hCconn hlap m⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_of_laplacianInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_of_laplacianInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_of_laplacianInput ``Submission.DifferentialGeometry.PDE.RicciFlow.shi_local_all_orders_curvature_scale_of_laplacianInput

end Corollary

end DifferentialGeometry.PDE.RicciFlow

end
