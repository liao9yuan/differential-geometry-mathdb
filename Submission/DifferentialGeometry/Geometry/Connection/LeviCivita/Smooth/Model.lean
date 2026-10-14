import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricCoord
import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section


namespace DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  Tensor.Coordinates.metricFlatContinuousEquiv (I := I) g x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w =
      g.inner x₀
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ v)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w) :=
  Tensor.Coordinates.metricFlatContinuousEquiv_apply (I := I) g x₀ v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv_apply ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatContinuousEquiv_apply

noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  Tensor.Coordinates.metricFlatModelInChart (I := I) g x₀ y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatModelInChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatModelInChart

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real)) :=
  Tensor.Coordinates.metricFlatModelInChart_center_eq (I := I) g x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_eq ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_eq

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_isInvertible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_isInvertible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_isInvertible ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_center_isInvertible


omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
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
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_apply_of_target
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v w : E) :
    metricFlatModelInChart (I := I) g x₀ y v w =
      g.inner ((extChartAt I x₀).symm y)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
          ((extChartAt I x₀).symm y) v)
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
          ((extChartAt I x₀).symm y) w) := by
  let p : M := (extChartAt I x₀).symm y
  have hp_source : p ∈ (extChartAt I x₀).source := by
    simpa [p] using (extChartAt I x₀).map_target hy
  have hp_frame : p ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hp_source
  have hpy : extChartAt I x₀ p = y := by
    simpa [p] using (extChartAt I x₀).right_inv hy
  have hcenter : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
    (extChartAt I x₀).left_inv hp_source
  rw [← hpy, hcenter]
  exact Tensor.Coordinates.flatChart_apply (I := I) g x₀ hp_frame v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_apply_of_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_apply_of_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_apply_of_target ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_apply_of_target


omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_contDiffWithinAt
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
  if env.contains `DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_contDiffWithinAt

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_contDiffWithinAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) y := by
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M -> Type _) x₀
  let b := Module.finBasis Real E
  let p : M := (extChartAt I x₀).symm y
  have hp_source : p ∈ (extChartAt I x₀).source := by
    simpa [p] using (extChartAt I x₀).map_target hy
  have hpE : p ∈ e.baseSet := by
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
  have hlocal :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => localMetricFlatBasis (I := I) e b g p) p :=
    localMetricFlatBasis_contMDiffAt (I := I) e b g hpE
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) y := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) x₀ hy
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => localMetricFlatBasis (I := I) e b g p) ∘
          (extChartAt I x₀).symm)
        (Set.range I) y :=
    hlocal.comp_contMDiffWithinAt (x := y) hsymm
  have heq :
      metricFlatModelInChart (I := I) g x₀ =ᶠ[𝓝[Set.range I] y]
        fun y' : E =>
          localMetricFlatBasis (I := I) e b g ((extChartAt I x₀).symm y') := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy] with y' hy'
    have hp'_source : (extChartAt I x₀).symm y' ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy'
    have hp'E : (extChartAt I x₀).symm y' ∈ e.baseSet := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp'_source
    ext v w
    calc
      metricFlatModelInChart (I := I) g x₀ y' v w =
          g.inner ((extChartAt I x₀).symm y')
            (e.symmL Real ((extChartAt I x₀).symm y') v)
            (e.symmL Real ((extChartAt I x₀).symm y') w) := by
            simpa [e] using metricFlatModelInChart_apply_of_target
              (I := I) g x₀ hy' v w
      _ =
          localMetricFlatBasis (I := I) e b g ((extChartAt I x₀).symm y') v w := by
            rw [localMetricFlatBasis_eq_inner (I := I) e b g hp'E v w]
  exact hcomp.contDiffWithinAt.congr_of_eventuallyEq heq
    (heq.self_of_nhdsWithin (extChartAt_target_subset_range x₀ hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt_of_mem ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_contDiffWithinAt_of_mem


omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y))
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis Real E).coord l))))
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
  simpa [εk, εl] using (contDiffWithinAt_const (c := εk)).clm_apply happ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_component_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_component_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_component_contDiffWithinAt ``Submission.DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_component_contDiffWithinAt

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (Module.finBasis Real E).coord i
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord j))) =
      (Module.finBasis Real E).coord j
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i))) := by
  simpa only [metricFlatModelInChart,
    Tensor.Coordinates.inverseMetricFlatModelInChartComponent] using
    Tensor.Coordinates.inverseMetricFlatModelInChart_component_center_eq_symm
      (I := I) g x₀ i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_component_center_eq_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_component_center_eq_symm target :: scope.openDecls } }

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis (I := I) g x₀ (coordinateFrameAtToBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
            (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))) := by
  simpa only [metricFlatModelInChart,
    Tensor.Coordinates.inverseMetricFlatModelInChartComponent] using
    Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_metricInverseInBasis_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_metricInverseInBasis_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_metricInverseInBasis_center ``Submission.DifferentialGeometry.Geometry.Connection.inverseMetricFlatModelInChart_metricInverseInBasis_center

noncomputable def metricFlatModelInChartComponent
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  metricFlatModelInChart (I := I) g x₀ y
    ((Module.finBasis Real E) i) ((Module.finBasis Real E) j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricFlatModelInChartComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricFlatModelInChartComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricFlatModelInChartComponent ``Submission.DifferentialGeometry.Geometry.Connection.metricFlatModelInChartComponent
end DifferentialGeometry.Geometry.Connection
