import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1 : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry_1

def CurvDerivBoundOn
    (K : Set M) (p : Nat)
    (h : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  forall x : M, x ∈ K -> curvDerivNorm (I := I) p h x <= C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOn

def CurvDerivBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (p : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    CurvDerivBoundOn (I := I) K p (gSeq i t) C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOnWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOnWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOnWindow ``Submission.DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundOnWindow

def CurvDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall p : Nat, CurvDerivBoundOnWindow (I := I) K β ψ gSeq p (C p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundsOnWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundsOnWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundsOnWindow ``Submission.DifferentialGeometry.CheegerGromovCompactness.CurvDerivBoundsOnWindow

def TwoTensorQuadBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop :=
  0 <= A /\
    forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |T i t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)| <=
            A * (gSeq i t).inner x v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.TwoTensorQuadBoundOnWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.TwoTensorQuadBoundOnWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.TwoTensorQuadBoundOnWindow ``Submission.DifferentialGeometry.CheegerGromovCompactness.TwoTensorQuadBoundOnWindow

structure MetricLogDerivativeAssumptions
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop where
  quad_bound : TwoTensorQuadBoundOnWindow (I := I) K β ψ gSeq T A
  metric_deriv :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          HasDerivAt
            (fun s : Real => (gSeq i s).inner x v v)
            ((-2 : Real) * T i t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v))
            t
  log_integrable :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) * T i s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /
                (gSeq i s).inner x v v)
            MeasureTheory.volume t0 t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricLogDerivativeAssumptions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricLogDerivativeAssumptions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricLogDerivativeAssumptions ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricLogDerivativeAssumptions

private theorem metric_factor_one_le
    {C A t t0 : Real}
    (hC : 1 <= C) (hA : 0 <= A) :
    1 <= metricEquivalenceFactor C A t t0 := by
  have harg_nonneg : 0 <= 2 * A * |t - t0| := by
    nlinarith [hA, abs_nonneg (t - t0)]
  have hexp : 1 <= Real.exp (2 * A * |t - t0|) :=
    Real.one_le_exp harg_nonneg
  have hprod : 0 <= (C - 1) * (Real.exp (2 * A * |t - t0|) - 1) :=
    mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hexp)
  rw [metricEquivalenceFactor]
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metric_factor_one_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metric_factor_one_le target :: scope.openDecls } }

private theorem metric_factor_inv_mul
    {C A t t0 g : Real}
    (hC : 1 <= C) :
    (metricEquivalenceFactor C A t t0)⁻¹ * g =
      Real.exp (-(2 * A) * |t - t0|) * (C⁻¹ * g) := by
  have hCne : C ≠ 0 := by nlinarith
  rw [metricEquivalenceFactor,
    show -(2 * A) * |t - t0| = -(2 * A * |t - t0|) by ring,
    Real.exp_neg]
  field_simp [hCne, Real.exp_ne_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metric_factor_inv_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metric_factor_inv_mul target :: scope.openDecls } }

private theorem metric_factor_mul
    {C A t t0 g : Real} :
    Real.exp ((2 * A) * |t - t0|) * (C * g) =
      metricEquivalenceFactor C A t t0 * g := by
  rw [metricEquivalenceFactor]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metric_factor_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metric_factor_mul target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOnWindow_of_log_derivative_bound
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) C)
    (hlog : MetricLogDerivativeAssumptions (I := I) K β ψ t0 gSeq T A) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq
      (fun t : Real => metricEquivalenceFactor C A t t0) := by
  intro i t ht
  refine ⟨metric_factor_one_le hC hlog.quad_bound.1, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  have hwindow : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc ht0 ht
  let f : Real -> Real := fun s => (gSeq i s).inner x v v
  let f' : Real -> Real :=
    fun s => (-2 : Real) * T i s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)
  have hf_pos : forall s : Real, s ∈ Set.uIcc t0 t -> 0 < f s := by
    intro s _hs
    exact (gSeq i s).pos x v hv
  have hf_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt f (f' s) s := by
    intro s hs
    exact hlog.metric_deriv i x hx v hv s (hwindow hs)
  have hA : 0 <= A := hlog.quad_bound.1
  have hbound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |f' s / f s| <= 2 * A := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hwindow hs
    have hquad := hlog.quad_bound.2 i s hswin x hx v
    have hden_pos : 0 < f s := hf_pos s hs
    have hnum :
        |(-2 : Real) * T i s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)| <=
          2 * (A * f s) := by
      calc
        |(-2 : Real) * T i s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)|
            = 2 * |T i s x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)| := by
              rw [abs_mul]
              norm_num
        _ <= 2 * (A * f s) :=
              mul_le_mul_of_nonneg_left hquad (by norm_num)
    calc
      |f' s / f s|
          = |f' s| / f s := by
            rw [abs_div, abs_of_pos hden_pos]
      _ <= (2 * (A * f s)) / f s :=
            div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
      _ = 2 * A := by
            field_simp [hden_pos.ne']
  have hscalar :
      Real.exp (-(2 * A) * |t - t0|) * f t0 <= f t /\
        f t <= Real.exp ((2 * A) * |t - t0|) * f t0 :=
    exp_bounds_of_log_deriv_bound f f' hf_pos hf_deriv hbound
  have h0 := (hequiv0 i).2 x hx v
  constructor
  · have hlow0 : C⁻¹ * gRef.inner x v v <= f t0 := h0.1
    have hlow_exp :
        Real.exp (-(2 * A) * |t - t0|) *
            (C⁻¹ * gRef.inner x v v) <=
          Real.exp (-(2 * A) * |t - t0|) * f t0 :=
      mul_le_mul_of_nonneg_left hlow0 (le_of_lt (Real.exp_pos _))
    calc
      (metricEquivalenceFactor C A t t0)⁻¹ * gRef.inner x v v
          = Real.exp (-(2 * A) * |t - t0|) *
              (C⁻¹ * gRef.inner x v v) :=
            metric_factor_inv_mul hC
      _ <= Real.exp (-(2 * A) * |t - t0|) * f t0 := hlow_exp
      _ <= f t := hscalar.1
  · have hhigh0 : f t0 <= C * gRef.inner x v v := h0.2
    have hhigh_exp :
        Real.exp ((2 * A) * |t - t0|) * f t0 <=
          Real.exp ((2 * A) * |t - t0|) *
            (C * gRef.inner x v v) :=
      mul_le_mul_of_nonneg_left hhigh0 (le_of_lt (Real.exp_pos _))
    calc
      f t <= Real.exp ((2 * A) * |t - t0|) * f t0 := hscalar.2
      _ <= Real.exp ((2 * A) * |t - t0|) *
          (C * gRef.inner x v v) := hhigh_exp
      _ = metricEquivalenceFactor C A t t0 * gRef.inner x v v :=
          metric_factor_mul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricUniformEquivalentOnWindow_of_log_derivative_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricUniformEquivalentOnWindow_of_log_derivative_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricUniformEquivalentOnWindow_of_log_derivative_bound ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricUniformEquivalentOnWindow_of_log_derivative_bound

structure MetricWindowBoundsAssumptions
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  compact : IsCompact K
  t0_mem : t0 ∈ Set.Icc β ψ
  equivC : Real
  equiv_at_t0 :
    forall i : Nat,
      MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) equivC
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p
  metric_at_t0 :
    MetricCovDerivBoundsAtTimeOn (I := I) K t0 gSeq gRef metricC
  curvC : Nat -> Real
  curvC_nonneg : forall p : Nat, 0 <= curvC p
  curv_on_window :
    CurvDerivBoundsOnWindow (I := I) K β ψ gSeq curvC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricWindowBoundsAssumptions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricWindowBoundsAssumptions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricWindowBoundsAssumptions ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricWindowBoundsAssumptions

structure MetricSpatialWindowBounds
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  metricC : Nat -> Real
  metric_on_window :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef metricC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSpatialWindowBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSpatialWindowBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSpatialWindowBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSpatialWindowBounds

structure MetricSpatialOrderWindowBounds
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  orderC : Nat -> Real
  orderC_nonneg : forall a : Nat, 0 <= orderC a
  order_on_window :
    forall a : Nat,
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a
        (orderC a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSpatialOrderWindowBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSpatialOrderWindowBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSpatialOrderWindowBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSpatialOrderWindowBounds

noncomputable def metricSpatialWindowBounds
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (H : MetricSpatialOrderWindowBounds (I := I) K β ψ gSeq gRef) :
    MetricSpatialWindowBounds (I := I) K β ψ gSeq gRef where
  B := H.B
  equiv_on_window := H.equiv_on_window
  metricC := metricCovCumulativeConstant H.orderC
  metric_on_window :=
    metricCovBoundsWindow_of_orderBounds (I := I) K β ψ gSeq gRef
      H.orderC H.orderC_nonneg H.order_on_window

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricSpatialWindowBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricSpatialWindowBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricSpatialWindowBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricSpatialWindowBounds

noncomputable def metricMixedDeriv
    (p q : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x :=
  let F :=
    Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x
  let Dfiber := Tensor0SBundle.tensor0SMetricData (I := I) gRef x (p + 2)
  letI : PreInnerProductSpace.Core Real F := Dfiber.toCore.toCore
  letI : SeminormedAddCommGroup F :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := Real) (F := F)
  letI : InnerProductSpace.Core Real F := Dfiber.toCore
  letI : NormedAddCommGroup F :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := Real) (F := F)
  letI : NormedSpace Real F :=
    InnerProductSpace.Core.toNormedSpace (𝕜 := Real) (F := F)
  iteratedDeriv (𝕜 := Real) (F := F) q
    (fun s : Real => metricCovDeriv (I := I) (h s) gRef p x) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv

noncomputable def metricMixedDerivNorm
    (p q : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
      (metricMixedDeriv (I := I) p q h gRef x t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm

omit [SigmaCompactSpace M] in
@[simp]
theorem metricMixedDerivNorm_zero
    (p : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    metricMixedDerivNorm (I := I) p 0 h gRef x t =
      metricCovDerivNorm (I := I) p (h t) gRef x := by
  simp [metricMixedDerivNorm, metricMixedDeriv, metricCovDerivNorm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm_zero ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedDerivNorm_zero

def MetricMixedDerivBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (p q : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall x : M, x ∈ K ->
      metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t <= C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundOnWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundOnWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundOnWindow ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundOnWindow

def MetricMixedDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Nat -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall p q : Nat,
      forall a : Nat, a <= p ->
        forall b : Nat, b <= q ->
          forall x : M, x ∈ K ->
            metricMixedDerivNorm (I := I) a b (gSeq i) gRef x t <= C p q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundsOnWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundsOnWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundsOnWindow ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivBoundsOnWindow

omit [SigmaCompactSpace M] in
theorem metricMixedWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (p q : Nat) (C : Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t <= C) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p q C := by
  intro i t ht x hx
  exact hpoint i t ht x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedWindow_of_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedWindow_of_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedWindow_of_pointwise ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedWindow_of_pointwise

omit [SigmaCompactSpace M] in
theorem metricMixedBoundsWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Nat -> Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall p q : Nat,
          forall a : Nat, a <= p ->
            forall b : Nat, b <= q ->
              forall x : M, x ∈ K ->
                metricMixedDerivNorm (I := I) a b (gSeq i) gRef x t <= C p q) :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef C := by
  intro i t ht p q a ha b hb x hx
  exact hpoint i t ht p q a ha b hb x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedBoundsWindow_of_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedBoundsWindow_of_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedBoundsWindow_of_pointwise ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedBoundsWindow_of_pointwise

def MetricMixedDerivOneEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall t : Real, t ∈ Set.Icc β ψ ->
    metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
      (-2 : Real) • nablaRic i t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivOneEvolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivOneEvolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivOneEvolutionOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricMixedDerivOneEvolutionOn

omit [SigmaCompactSpace M] in
theorem metricMixedDeriv_one_eq_of_evolution
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat}
    {nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic)
    {i : Nat} {x : M} (hx : x ∈ K) {t : Real} (ht : t ∈ Set.Icc β ψ) :
    metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
      (-2 : Real) • nablaRic i t x := by
  exact hmixed i x hx t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv_one_eq_of_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv_one_eq_of_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv_one_eq_of_evolution ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedDeriv_one_eq_of_evolution

def metricMixedOneConstant (Cpp Csp0 Cppp : Real) : Real :=
  2 * (Cpp * Csp0 + Cppp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedOneConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedOneConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedOneConstant ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedOneConstant

omit [SigmaCompactSpace M] in
theorem metricMixedOneWindow_of_ric_bound
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat} {Csp0 : Real}
    {nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (Cpp Cppp : Real)
    (Cpp_nonneg : 0 <= Cpp)
    (ric_bound :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) <=
            Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x + Cppp)
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic)
    (hspatial :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p Csp0) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Cpp Csp0 Cppp) := by
  refine
    metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Cpp Csp0 Cppp) ?_
  intro i t ht x hx
  have hmixed_eq :
      metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
        (-2 : Real) • nablaRic i t x :=
    metricMixedDeriv_one_eq_of_evolution (I := I)
      (K := K) (β := β) (ψ := ψ) (gSeq := gSeq) (gRef := gRef)
      (p := p) (nablaRic := nablaRic) hmixed hx ht
  have hnorm_eq :
      metricMixedDerivNorm (I := I) p 1 (gSeq i) gRef x t =
        2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) := by
    unfold metricMixedDerivNorm
    rw [hmixed_eq]
    rw [Tensor0SBundle.sqrt_normSq0S_smul]
    norm_num
  have hric :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i t x)) <=
        Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x + Cppp :=
    ric_bound i t ht x hx
  have hsp :
      metricCovDerivNorm (I := I) p (gSeq i t) gRef x <= Csp0 :=
    hspatial i t ht x hx
  have hric_sp :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i t x)) <=
        Cpp * Csp0 + Cppp := by
    have hmul :
        Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x <=
          Cpp * Csp0 :=
      mul_le_mul_of_nonneg_left hsp Cpp_nonneg
    exact le_trans hric (by linarith)
  have hmain :
      2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) <=
        metricMixedOneConstant Cpp Csp0 Cppp := by
    unfold metricMixedOneConstant
    exact mul_le_mul_of_nonneg_left hric_sp (by norm_num : (0 : Real) <= 2)
  simpa [hnorm_eq] using hmain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricMixedOneWindow_of_ric_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricMixedOneWindow_of_ric_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricMixedOneWindow_of_ric_bound ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricMixedOneWindow_of_ric_bound

structure MetricMixedWindowBounds
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  metricC : Nat -> Nat -> Real
  mixed_on_window :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef metricC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricMixedWindowBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricMixedWindowBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricMixedWindowBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricMixedWindowBounds

def metricFirstOrderConstant
    (Ca Cb R timeRadius M0 : Real) : Real :=
  Real.sqrt (Cb ^ 3) *
    (2 *
      (3 * R * timeRadius +
        (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * M0)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricFirstOrderConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricFirstOrderConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricFirstOrderConstant ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricFirstOrderConstant

end FixedDomain

end CheegerGromovCompactness
end DifferentialGeometry
