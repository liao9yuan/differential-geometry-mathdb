import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Ball.Basic
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Tensor.RicciIdentity
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def HasCurvDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (k : Nat)
    (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  forall x : X.M, curvDerivNorm (I := I) k X.metric x <= C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound

namespace HasCurvDerivBound

private theorem sqrt_le_of_sq_le_mul {q A : Real}
    (hq : 0 <= q) (hA : 0 <= A) (h : q ^ 2 <= A * q) :
    q <= A := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0]
    exact hA
  · exact le_of_mul_le_mul_right (by simpa [pow_two] using h) hqpos

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.sqrt_le_of_sq_le_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.sqrt_le_of_sq_le_mul target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem inner_self_nonneg
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    0 <= g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv]
    simp
  · exact le_of_lt (g.pos x v hv)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.inner_self_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.inner_self_nonneg target :: scope.openDecls } }

theorem apply_le
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {k : Nat} {C : Real}
    (hX : HasCurvDerivBound (I := I) X k C) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    ∀ (x : X.M) (v : Fin (k + 4) -> TangentSpace I x),
      |curvCovDeriv (I := I) (M := X.M) X.metric k x v| <=
        C * ∏ a : Fin (k + 4),
          Real.sqrt (X.metric.inner x (v a) (v a)) := by
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace H X.M := X.charted
  let : IsManifold I ∞ X.M := X.smooth
  let : SigmaCompactSpace X.M := X.sigmaCompact
  let : T2Space X.M := X.t2
  intro x v
  calc
    |curvCovDeriv (I := I) (M := X.M) X.metric k x v| <=
        curvDerivNorm (I := I) (M := X.M) k X.metric x *
          ∏ a : Fin (k + 4),
            Real.sqrt (X.metric.inner x (v a) (v a)) :=
      curv_apply_le (I := I) X.metric k x v
    _ <= C * ∏ a : Fin (k + 4),
          Real.sqrt (X.metric.inner x (v a) (v a)) :=
      mul_le_mul_of_nonneg_right (hX x)
        (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.apply_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.apply_le

section PointwiseCurvature

variable [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem riemann_op_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {C : Real} (hP : HasCurvDerivBound (I := I) P 0 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (x : P.M) (X Y Z : TangentSpace I x),
      let R :=
        DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita
            (I := I) P.metric) x X Y Z
      Real.sqrt (P.metric.inner x R R) <=
        C * Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : T2Space P.M := P.t2
  intro x X Y Z
  let R :=
    DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita
        (I := I) P.metric) x X Y Z
  let q := Real.sqrt (P.metric.inner x R R)
  let A :=
    C * Real.sqrt (P.metric.inner x X X) *
      Real.sqrt (P.metric.inner x Y Y) *
      Real.sqrt (P.metric.inner x Z Z)
  have hC : 0 <= C := by
    exact (Real.sqrt_nonneg
      (curvDerivNormSq (I := I) (M := P.M) 0 P.metric x)).trans (hP x)
  have hA : 0 <= A := by
    dsimp [A]
    positivity
  have hRR : 0 <= P.metric.inner x R R :=
    inner_self_nonneg (I := I) P.metric x R
  have hbound := apply_le (I := I) P hP x
    (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z R)
  rw [curvZero_apply] at hbound
  have hprod :
      (∏ a : Fin 4,
          Real.sqrt (P.metric.inner x
            (DifferentialGeometry.Geometry.Curvature.vec4
              (I := I) X Y Z R a)
            (DifferentialGeometry.Geometry.Curvature.vec4
              (I := I) X Y Z R a))) =
        Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) * q := by
    simp [DifferentialGeometry.Geometry.Curvature.vec4,
      Fin.prod_univ_succ, q, mul_assoc]
  rw [hprod, abs_of_nonneg hRR] at hbound
  have hquad : q ^ 2 <= A * q := by
    rw [show q ^ 2 = P.metric.inner x R R from by
      exact Real.sq_sqrt hRR]
    simpa [A, mul_assoc] using hbound
  exact sqrt_le_of_sq_le_mul (Real.sqrt_nonneg _) hA hquad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.riemann_op_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.riemann_op_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.riemann_op_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.riemann_op_le

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem nabla_riemann_op_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {C : Real} (hP : HasCurvDerivBound (I := I) P 1 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (x : P.M) (D X Y Z : TangentSpace I x),
      let R :=
        DifferentialGeometry.Geometry.Curvature.nablaRiemannOp
          (I := I) P.metric x D X Y Z
      Real.sqrt (P.metric.inner x R R) <=
        C * Real.sqrt (P.metric.inner x D D) *
          Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : T2Space P.M := P.t2
  intro x D X Y Z
  let R :=
    DifferentialGeometry.Geometry.Curvature.nablaRiemannOp
      (I := I) P.metric x D X Y Z
  let q := Real.sqrt (P.metric.inner x R R)
  let A :=
    C * Real.sqrt (P.metric.inner x D D) *
      Real.sqrt (P.metric.inner x X X) *
      Real.sqrt (P.metric.inner x Y Y) *
      Real.sqrt (P.metric.inner x Z Z)
  have hC : 0 <= C := by
    exact (Real.sqrt_nonneg
      (curvDerivNormSq (I := I) (M := P.M) 1 P.metric x)).trans (hP x)
  have hA : 0 <= A := by
    dsimp [A]
    positivity
  have hRR : 0 <= P.metric.inner x R R :=
    inner_self_nonneg (I := I) P.metric x R
  have hbound := apply_le (I := I) P hP x
    (DifferentialGeometry.Geometry.Curvature.vec5 (I := I) D X Y Z R)
  rw [curvOne_apply] at hbound
  have hprod :
      (∏ a : Fin 5,
          Real.sqrt (P.metric.inner x
            (DifferentialGeometry.Geometry.Curvature.vec5
              (I := I) D X Y Z R a)
            (DifferentialGeometry.Geometry.Curvature.vec5
              (I := I) D X Y Z R a))) =
        Real.sqrt (P.metric.inner x D D) *
          Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) * q := by
    simp [DifferentialGeometry.Geometry.Curvature.vec5,
      Fin.prod_univ_succ, q, mul_assoc]
  rw [hprod, abs_of_nonneg hRR] at hbound
  have hquad : q ^ 2 <= A * q := by
    rw [show q ^ 2 = P.metric.inner x R R from by
      exact Real.sq_sqrt hRR]
    simpa [A, mul_assoc] using hbound
  exact sqrt_le_of_sq_le_mul (Real.sqrt_nonneg _) hA hquad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.nabla_riemann_op_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.nabla_riemann_op_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.nabla_riemann_op_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HasCurvDerivBound.nabla_riemann_op_le

end PointwiseCurvature

end HasCurvDerivBound

theorem rm04Bound_of_curv0
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) {C : Real}
    (hX : HasCurvDerivBound (I := I) X 0 C) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric C := by
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace H X.M := X.charted
  let : IsManifold I ∞ X.M := X.smooth
  let : SigmaCompactSpace X.M := X.sigmaCompact
  let : T2Space X.M := X.t2
  intro x
  simpa [Geometry.Riemannian.VolumeComparison.Rm04GlobalBound,
    HasCurvDerivBound, curvDerivNorm, curvDerivNormSq, curvCovDeriv,
    DifferentialGeometry.Geometry.Curvature.metricRm04_apply] using hX x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_curv0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_curv0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_curv0 ``Submission.DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_curv0

structure BoundedGeometry
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall k : Nat, HasCurvDerivBound (I := I) X k (C k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.BoundedGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.BoundedGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.BoundedGeometry ``Submission.DifferentialGeometry.CheegerGromovCompactness.BoundedGeometry

theorem rm04Bound_of_geom
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (hX : BoundedGeometry (I := I) X) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) X (hX.bound 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_geom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_geom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_geom ``Submission.DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_geom

structure SeqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasCurvDerivBound (I := I) (X.obj i) k (C k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry

namespace SeqBoundedGeometry

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (f : Nat -> Nat) :
    SeqBoundedGeometry (I := I) (X.subseq f) where
  C := hX.C
  nonneg := hX.nonneg
  bound := by
    intro i k
    simpa [PointedRiemannianSeq.subseq] using hX.bound (f i) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBoundedGeometry.subseq

end SeqBoundedGeometry

theorem rm04Bound_of_seq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (i : Nat) :
    letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
    letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
    letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
    letI : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
    letI : T2Space (X.obj i).M := (X.obj i).t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := (X.obj i).M) (X.obj i).metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) (X.obj i) (hX.bound i 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_seq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_seq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_seq ``Submission.DifferentialGeometry.CheegerGromovCompactness.rm04Bound_of_seq

end CheegerGromovCompactness
end DifferentialGeometry
