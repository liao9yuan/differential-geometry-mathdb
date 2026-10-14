import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import Submission.DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel
import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.RawFields
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import Mathlib.Geometry.Manifold.VectorBundle.Hom

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  let e := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt Real x₀
    (FiberBundle.mem_baseSet_trivializationAt' x₀)
  ((e.symm.toLinearEquiv.trans (metricFlatEquiv (I := I) g x₀)).trans
      e.symm.toLinearEquiv.dualMap |>.trans
    (LinearMap.toContinuousLinearMap :
      (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real))).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv ``Submission.DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv

theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w =
      g.inner x₀
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ v)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w) := by
  have hx : x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
    simp
  let e := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt Real x₀ hx
  change ((metricFlatEquiv (I := I) g x₀) (e.symm v)) (e.symm w) = _
  rw [metricFlatEquiv_apply]
  rw [Trivialization.symm_continuousLinearEquivAt_eq _ hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.metricFlatContinuousEquiv_apply

noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  (_root_.FiberBundle.trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
      ⟨(extChartAt I x₀).symm y, g.inner ((extChartAt I x₀).symm y)⟩).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart ``Submission.DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart

theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real)) := by
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  ext v w
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀ x₀ x₀ x₀
        (g.inner x₀) v) w =
      ((metricFlatContinuousEquiv (I := I) g x₀) v) w
  have hxT :
      x₀ ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simp
  have hxDual :
      x₀ ∈ (_root_.FiberBundle.trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  rw [metricFlatContinuousEquiv_apply]
  simp only [hom_trivializationAt, Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply, Function.comp_apply]
  have hxR : x₀ ∈ (_root_.FiberBundle.trivializationAt Real (fun _ : M => Real) x₀).baseSet := by
    simp
  rw [Trivialization.continuousLinearMapAt_apply]
  rw [(_root_.FiberBundle.trivializationAt Real (fun _ : M => Real) x₀).coe_linearMapAt_of_mem
    (R := Real) hxR]
  simp only [Trivialization.symmL_apply _ hxT,
    Trivial.fiberBundle_trivializationAt']
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_eq ``Submission.DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_eq

omit [FiniteDimensional ℝ E] in
theorem flatChart_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (v w : E) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v w =
      g.inner x
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
  have hx_source : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x) = x :=
    (extChartAt I x₀).left_inv hx_source
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  have hxT :
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hxDual :
      x ∈ (_root_.FiberBundle.trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  simp only [hom_trivializationAt, Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply, Function.comp_apply]
  simp only [Trivialization.symmL_apply _ hxT,
    Trivial.fiberBundle_trivializationAt']
  have hxR : x ∈ (Trivial.trivialization M Real).baseSet := by
    simp
  rw [Trivialization.continuousLinearMapAt_apply_of_mem Real _ hxR]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.flatChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.flatChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.flatChart_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.flatChart_apply

theorem flatChart_inv
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)).IsInvertible := by
  have : CompleteSpace (E →L[Real] Real) := inferInstance
  let A : E →ₗ[Real] (E →L[Real] Real) :=
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)).toLinearMap
  have hxT :
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hker : LinearMap.ker A = ⊥ := by
    ext v
    constructor
    · intro hv
      change A v = 0 at hv
      have hself :
          metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v v = 0 := by
        exact congrArg (fun L : E →L[Real] Real => L v) hv
      have hinner :
          g.inner x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) = 0 := by
        rw [← flatChart_apply (I := I) g x₀ hx v v]
        exact hself
      by_contra hvne
      have hsymm_ne :
          (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v ≠ 0 := by
        intro hzero
        have hmap := congrArg
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
            Real x) hzero
        have hcancel :
            (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
                Real x
              ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) = v :=
          (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt_symmL
            (R := Real) hxT v
        rw [hcancel] at hmap
        exact hvne (by simpa using hmap)
      exact False.elim ((ne_of_gt (g.pos x
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
        hsymm_ne)) hinner)
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      simp [A, hv0]
  have hdim :
      Module.finrank Real E = Module.finrank Real (E →L[Real] Real) := by
    calc
      Module.finrank Real E = Module.finrank Real (Module.Dual Real E) :=
        Subspace.dual_finrank_eq.symm
      _ = Module.finrank Real (E →L[Real] Real) :=
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real)).finrank_eq
  let Aequiv : E ≃ₗ[Real] (E →L[Real] Real) :=
    A.linearEquivOfInjective (LinearMap.ker_eq_bot.mp hker) hdim
  let Acle : E ≃L[Real] (E →L[Real] Real) :=
    Aequiv.toContinuousLinearEquiv
  have hA : (Acle : E →L[Real] E →L[Real] Real) =
      metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) := by
    ext v w
    change Aequiv v w =
      metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v w
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  rw [← hA]
  exact ContinuousLinearMap.isInvertible_equiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.flatChart_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.flatChart_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.flatChart_inv ``Submission.DifferentialGeometry.Tensor.Coordinates.flatChart_inv

theorem coordBasis_model
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordinateFrameAtBasis (I := I) x₀ hx i =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x
        ((Module.finBasis Real E) i) := by
  rw [coordinateFrameAt_basis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) hx i]
  have hx_source : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  exact (congrArg
    (fun L : E →L[Real] TangentSpace I x => L ((Module.finBasis Real E) i))
    (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_source)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordBasis_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordBasis_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordBasis_model ``Submission.DifferentialGeometry.Tensor.Coordinates.coordBasis_model

theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_isInvertible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_isInvertible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_isInvertible ``Submission.DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_center_isInvertible


omit [FiniteDimensional ℝ E] in
theorem metricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := _root_.FiberBundle.trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            _root_.Bundle.TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x₀ :=
    (g.contMDiff.contMDiffAt (x := x₀)).of_le (by simp)
  have hcoord :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2) x₀ :=
    by
      rw [_root_.Bundle.contMDiffAt_totalSpace] at hg
      simpa [e] using hg.2
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => (e ⟨p, g.inner p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt
      (x := extChartAt I x₀ x₀) hsymm
  exact hcomp.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_contDiffWithinAt ``Submission.DifferentialGeometry.Tensor.Coordinates.metricFlatModelInChart_contDiffWithinAt


theorem inverseMetricFlatModelInChart_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact
    (metricFlatModelInChart_center_isInvertible (I := I) g x₀).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt
        (x := extChartAt I x₀ x₀)
        (metricFlatModelInChart_contDiffWithinAt (I := I) g x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_contDiffWithinAt ``Submission.DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_contDiffWithinAt

noncomputable def inverseMetricFlatModelInChartComponent
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  (Module.finBasis Real E).coord k
    ((ContinuousLinearMap.inverse
        (metricFlatModelInChart (I := I) g x₀ y))
      (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent ``Submission.DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent


theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (inverseMetricFlatModelInChartComponent (I := I) g x₀ k l)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let εl : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)
  let εk : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hinv := inverseMetricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have happ :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          (ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y)) εl)
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  unfold inverseMetricFlatModelInChartComponent
  exact (contDiffWithinAt_const (c := εk)).clm_apply happ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_contDiffWithinAt ``Submission.DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_contDiffWithinAt

theorem gInvComp_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀ := by
  have : CompleteSpace E := FiniteDimensional.complete Real E
  let f : E -> Real :=
    inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
  have hf :
      ContDiffWithinAt Real ∞ f (Set.range I) (extChartAt I x₀ x₀) :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ k l
  have hchart :
      ContMDiffWithinAt I 𝓘(Real, E) ∞ (extChartAt I x₀)
        (extChartAt I x₀).source x₀ :=
    (contMDiffAt_extChartAt (I := I) (x := x₀)).contMDiffWithinAt
  have hcomp :
      ContMDiffWithinAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀)
        (extChartAt I x₀).source x₀ := by
    exact hf.comp_contMDiffWithinAt hchart (by
      intro y hy
      exact extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hy))
  have hcompAt :
      ContMDiffAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀) x₀ :=
    hcomp.contMDiffAt ((isOpen_extChartAt_source (I := I) x₀).mem_nhds
      (mem_extChartAt_source (I := I) x₀))
  simpa [f, Function.comp_def] using hcompAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.gInvComp_contMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.gInvComp_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.gInvComp_contMDiffAt ``Submission.DifferentialGeometry.Tensor.Coordinates.gInvComp_contMDiffAt

theorem gInvComp_mdiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀ := by
  exact (gInvComp_contMDiffAt (I := I) g x₀ k l).mdifferentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt ``Submission.DifferentialGeometry.Tensor.Coordinates.gInvComp_mdiffAt

theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChartComponent (I := I) g x₀ i j
        (extChartAt I x₀ x₀) =
      inverseMetricFlatModelInChartComponent (I := I) g x₀ j i
        (extChartAt I x₀ x₀) := by
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  simp only [inverseMetricFlatModelInChartComponent]
  rw [hInv]
  calc
    (Module.finBasis Real E).coord i (A.symm (ε j))
        = (ε i) (A.symm (ε j)) := rfl
    _ = (A (A.symm (ε i))) (A.symm (ε j)) := by
          rw [A.apply_symm_apply]
    _ = g.inner x₀
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε i)))
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε j))) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = g.inner x₀
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε j)))
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε i))) := by
          exact g.symm x₀
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε i)))
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε j)))
    _ = (A (A.symm (ε j))) (A.symm (ε i)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = (ε j) (A.symm (ε i)) := by
          rw [A.apply_symm_apply]
    _ = (Module.finBasis Real E).coord j (A.symm (ε i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_center_eq_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_center_eq_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_center_eq_symm ``Submission.DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component_center_eq_symm

theorem gInvChart_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChartComponent (I := I) g x₀ i j
        (extChartAt I x₀ x) =
      inverseMetricFlatModelInChartComponent (I := I) g x₀ j i
        (extChartAt I x₀ x) := by
  let A : E →L[Real] (E →L[Real] Real) :=
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv : A.IsInvertible := flatChart_inv (I := I) g x₀ hx
  have hA_sym (v w : E) : A v w = A w v := by
    calc
      A v w =
          g.inner x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            exact flatChart_apply (I := I) g x₀ hx v w
      _ =
          g.inner x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) := by
            exact g.symm x _ _
      _ = A w v := by
            rw [flatChart_apply (I := I) g x₀ hx w v]
  simp only [inverseMetricFlatModelInChartComponent]
  calc
    (Module.finBasis Real E).coord i (ContinuousLinearMap.inverse A (ε j))
        = (ε i) (ContinuousLinearMap.inverse A (ε j)) := rfl
    _ = (A (ContinuousLinearMap.inverse A (ε i)))
          (ContinuousLinearMap.inverse A (ε j)) := by
          rw [hInv.self_apply_inverse]
    _ = (A (ContinuousLinearMap.inverse A (ε j)))
          (ContinuousLinearMap.inverse A (ε i)) := by
          exact hA_sym (ContinuousLinearMap.inverse A (ε i))
            (ContinuousLinearMap.inverse A (ε j))
    _ = (ε j) (ContinuousLinearMap.inverse A (ε i)) := by
          rw [hInv.self_apply_inverse]
    _ = (Module.finBasis Real E).coord j (ContinuousLinearMap.inverse A (ε i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.gInvChart_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.gInvChart_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.gInvChart_symm ``Submission.DifferentialGeometry.Tensor.Coordinates.gInvChart_symm

theorem gInvBasisAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    MetricInverseInBasis (I := I) g x (coordinateFrameAtBasis (I := I) x₀ hx)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ x)) := by
  classical
  let A : E →L[Real] (E →L[Real] Real) :=
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
      (extChartAt I x₀ x)
  have hInv : A.IsInvertible := flatChart_inv (I := I) g x₀ hx
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.inverse (ε l)) := by
    rfl
  have hA_sym (v w : E) : A v w = A w v := by
    calc
      A v w =
          g.inner x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            exact flatChart_apply (I := I) g x₀ hx v w
      _ =
          g.inner x
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) := by
            exact g.symm x _ _
      _ = A w v := by
            rw [flatChart_apply (I := I) g x₀ hx w v]
  have hmetric (i j : CoordinateIdx (𝕜 := Real) E) :
      g.inner x ((coordinateFrameAtBasis (I := I) x₀ hx) i)
          ((coordinateFrameAtBasis (I := I) x₀ hx) j) =
        A ((Module.finBasis Real E) i) ((Module.finBasis Real E) j) := by
    rw [coordBasis_model (I := I) x₀ hx i]
    rw [coordBasis_model (I := I) x₀ hx j]
    rw [flatChart_apply (I := I) g x₀ hx]
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.inverse (ε l))
          = (ε k) (A.inverse (ε l)) := rfl
      _ = (A (A.inverse (ε k))) (A.inverse (ε l)) := by
            rw [hInv.self_apply_inverse]
      _ = (A (A.inverse (ε l))) (A.inverse (ε k)) := by
            exact hA_sym (A.inverse (ε k)) (A.inverse (ε l))
      _ = (ε l) (A.inverse (ε k)) := by
            rw [hInv.self_apply_inverse]
      _ = (Module.finBasis Real E).coord l (A.inverse (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x ((coordinateFrameAtBasis (I := I) x₀ hx) i)
            ((coordinateFrameAtBasis (I := I) x₀ hx) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    simp only [hmetric, hginv]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.inverse (ε j)))
          = A ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (A ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.inverse (ε j)))
                ((Module.finBasis Real E) k)
            calc
              A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.inverse (ε j))
                  =
                (Module.finBasis Real E).coord k (A.inverse (ε j)) *
                  A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by ring
              _ =
                (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                  A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by simp
              _ =
                A ((Module.finBasis Real E) i)
                  ((Module.finBasis Real E).coord k (A.inverse (ε j)) •
                    (Module.finBasis Real E) k) := hmap.symm
      _ = A ((Module.finBasis Real E) i) (A.inverse (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                    (Module.finBasis Real E) k) = A.inverse (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.inverse (ε j))
            exact congrArg (fun v => A ((Module.finBasis Real E) i) v) hsum
      _ = (A (A.inverse (ε j))) ((Module.finBasis Real E) i) := by
            exact hA_sym ((Module.finBasis Real E) i) (A.inverse (ε j))
      _ = (ε j) ((Module.finBasis Real E) i) := by
            rw [hInv.self_apply_inverse]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := fun h => hij h.symm
              simp [ε, hij, hji]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x ((coordinateFrameAtBasis (I := I) x₀ hx) k)
            ((coordinateFrameAtBasis (I := I) x₀ hx) j))
          =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x ((coordinateFrameAtBasis (I := I) x₀ hx) j)
            ((coordinateFrameAtBasis (I := I) x₀ hx) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x ((coordinateFrameAtBasis (I := I) x₀ hx) k)
              ((coordinateFrameAtBasis (I := I) x₀ hx) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.gInvBasisAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.gInvBasisAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.gInvBasisAt ``Submission.DifferentialGeometry.Tensor.Coordinates.gInvBasisAt

theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis (I := I) g x₀ (coordinateFrameAtToBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ x₀)) := by
  classical
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
      (extChartAt I x₀ x₀)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  have hbasis (i : CoordinateIdx (𝕜 := Real) E) :
      coordinateFrameAtToBasis (I := I) x₀ i =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀
          ((Module.finBasis Real E) i) :=
    coordBasis_model (I := I) x₀ (coordinateFrameAt_mem (I := I) x₀) i
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.symm (ε l)) := by
    dsimp [gInv, inverseMetricFlatModelInChartComponent]
    simpa [extChartAt] using
      congrArg (fun L : (E →L[Real] Real) →L[Real] E =>
        (Module.finBasis Real E).coord k (L (ε l))) hInv
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.symm (ε l))
          = (ε k) (A.symm (ε l)) := rfl
      _ = (A (A.symm (ε k))) (A.symm (ε l)) := by
            rw [A.apply_symm_apply]
      _ = g.inner x₀
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε k)))
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε l))) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = g.inner x₀
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε l)))
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε k))) := by
            exact g.symm x₀
              ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε k)))
              ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ (A.symm (ε l)))
      _ = (A (A.symm (ε l))) (A.symm (ε k)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = (ε l) (A.symm (ε k)) := by
            rw [A.apply_symm_apply]
      _ = (Module.finBasis Real E).coord l (A.symm (ε k)) := rfl
  have hA_sym (v w : E) : A v w = A w v := by
    rw [metricFlatContinuousEquiv_apply (I := I) g x₀,
      metricFlatContinuousEquiv_apply (I := I) g x₀]
    exact g.symm x₀
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ v)
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w)
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((coordinateFrameAtToBasis (I := I) x₀) i)
            ((coordinateFrameAtToBasis (I := I) x₀) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    simp only [hbasis, hginv, ← metricFlatContinuousEquiv_apply (I := I) g x₀]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.symm (ε j)))
          = A ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.symm (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (A ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.symm (ε j)))
                ((Module.finBasis Real E) k)
            calc
              A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.symm (ε j))
                  = (Module.finBasis Real E).coord k (A.symm (ε j)) *
                      A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by ring
              _ = (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by simp
              _ = A ((Module.finBasis Real E) i)
                    ((Module.finBasis Real E).coord k (A.symm (ε j)) •
                      (Module.finBasis Real E) k) := hmap.symm
      _ = A ((Module.finBasis Real E) i) (A.symm (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    (Module.finBasis Real E) k) = A.symm (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.symm (ε j))
            exact congrArg (A ((Module.finBasis Real E) i)) hsum
      _ = A (A.symm (ε j)) ((Module.finBasis Real E) i) :=
            hA_sym _ _
      _ = ε j ((Module.finBasis Real E) i) := by
            rw [A.apply_symm_apply]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := by exact fun h => hij h.symm
              simp [ε, hji, hij]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x₀ ((coordinateFrameAtToBasis (I := I) x₀) k)
            ((coordinateFrameAtToBasis (I := I) x₀) j))
          = ∑ k : CoordinateIdx (𝕜 := Real) E,
              g.inner x₀ ((coordinateFrameAtToBasis (I := I) x₀) j)
                ((coordinateFrameAtToBasis (I := I) x₀) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x₀ ((coordinateFrameAtToBasis (I := I) x₀) k)
              ((coordinateFrameAtToBasis (I := I) x₀) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center ``Submission.DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center


def metricCompForMetricInFrame
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  g.inner x (frame i x) (frame j x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame

theorem gInvBasisNhds
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M => ∑ k : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChartComponent (I := I) g x₀ i k
          (extChartAt I x₀ y) *
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) y k j) =ᶠ[𝓝 x₀]
      fun _ : M => if i = j then 1 else 0 := by
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
    (coordinateFrameAt_mem (I := I) x₀)] with y hy
  have h := (gInvBasisAt (I := I) g x₀ hy i j).1
  simpa [metricCompForMetricInFrame, coordinateFrameAt_basis_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.gInvBasisNhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.gInvBasisNhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.gInvBasisNhds ``Submission.DifferentialGeometry.Tensor.Coordinates.gInvBasisNhds

end Components

end
end DifferentialGeometry.Tensor.Coordinates
