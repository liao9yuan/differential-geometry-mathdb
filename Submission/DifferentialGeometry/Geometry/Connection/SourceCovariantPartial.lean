import Submission.DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import Submission.DifferentialGeometry.Geometry.Metric.SourcePartialCoordinates
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Coordinates.FixedChartIdentities
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionAtBasepoint
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


def sourceCovariantPartial (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : A → M) (z v w : A) : TangentSpace 𝓘(ℝ, E) (U z) :=
  sourceSectionCovariantDerivative g U (fun q => mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U q w) z v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sourceCovariantPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sourceCovariantPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sourceCovariantPartial ``Submission.DifferentialGeometry.Geometry.sourceCovariantPartial

omit [FiniteDimensional ℝ E] in
private theorem chartCoord_self (p : M) (X : TangentSpace 𝓘(ℝ, E) p) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ p X = X :=
  (DifferentialGeometry.Geometry.Connection.trivToE_basepoint p X).trans
    (tangentSpaceModelContinuousLinearEquiv_apply p X)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.chartCoord_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.chartCoord_self target :: scope.openDecls } }



theorem sourceCovariantPartial_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : A → M} {s : Set A}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U s)
    {z : A} (hz : z ∈ s) (v w : A) :
    let F := (extChartAt 𝓘(ℝ, E) (U z)) ∘ U
    (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ (U z)
        (sourceCovariantPartial g U z v w) =
      fderiv ℝ (fun q => fderiv ℝ F q w) z v +
        chartChristoffelContraction g (U z) (fderiv ℝ F z v) (fderiv ℝ F z w) (F z) := by
  let F := (extChartAt 𝓘(ℝ, E) (U z)) ∘ U
  have hUz := (hU z hz).contMDiffAt (hs.mem_nhds hz)
  have hF : ContDiffAt ℝ 2 F z :=
    ((contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := U z)).comp z hUz).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hrepnear : (fun q =>
      (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ (U q)
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U q w)) =ᶠ[𝓝 z] (fun q => fderiv ℝ F q w) := by
    filter_upwards [hs.mem_nhds hz, hUz.continuousAt
      ((chartAt E (U z)).open_source.mem_nhds (mem_chart_source E (U z)))] with q hq hchart
    exact congrArg (fun L => L w) (chartCoord_source_mfderiv
      (((hU q hq).contMDiffAt (hs.mem_nhds hq)).mdifferentiableAt (by simp)) (U z) hchart)
  let line : ℝ → A := fun t => z + t • v
  have hl0 : line 0 = z := by simp [line]
  have hl : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have ht : _root_.Filter.Tendsto line (𝓝 0) (𝓝 z) := by
    have h := hl.continuousAt
    change _root_.Filter.Tendsto line (𝓝 0) (𝓝 (line 0)) at h
    rwa [hl0] at h
  have hrep : chartRepAt (U ∘ line) (fun t => mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U (line t) w) 0 =ᶠ[𝓝 0]
      (fun t => fderiv ℝ F (line t) w) := by
    filter_upwards [ht.eventually hrepnear] with t hq
    change (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U (line 0))).continuousLinearMapAt ℝ
      (U (line t)) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U (line t) w) = _
    rw [hl0]
    exact hq
  have hdpartial : DifferentiableAt ℝ (fun q => fderiv ℝ F q w) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hrepderiv := (hdpartial.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hl hl0.symm).congr_of_eventuallyEq hrep
  have hcurvederiv : HasDerivAt (chartCurve (I := 𝓘(ℝ, E)) (U z) (U ∘ line))
      (fderiv ℝ F z v) 0 :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq
      (x := 0) hl hl0.symm
  have hcov := covDerivAlong_chartCoord g (U ∘ line)
    (fun t => mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U (line t) w) 0
  rw [chartCoord_self] at hcov ⊢
  refine hcov.trans ?_
  rw [chartCovDerivAlong_def, hrepderiv.deriv, hrep.eq_of_nhds]
  simp only [Function.comp_apply, hl0]
  rw [hcurvederiv.deriv]
  simp only [hl0, chartCurve_def, Function.comp_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sourceCovariantPartial_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sourceCovariantPartial_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sourceCovariantPartial_chart ``Submission.DifferentialGeometry.Geometry.sourceCovariantPartial_chart




theorem sourceCovariantPartial_symm
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : A → M} {s : Set A}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U s)
    {z : A} (hz : z ∈ s) (v w : A) :
    sourceCovariantPartial g U z v w = sourceCovariantPartial g U z w v := by
  let F := (extChartAt 𝓘(ℝ, E) (U z)) ∘ U
  have hF : ContDiffAt ℝ 2 F z :=
    ((contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := U z)).comp z
      ((hU z hz).contMDiffAt (hs.mem_nhds hz))).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpartial (a b : A) : fderiv ℝ (fun q => fderiv ℝ F q a) z b =
      fderiv ℝ (fderiv ℝ F) z b a := by
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  have hvw := sourceCovariantPartial_chart g hs hU hz v w
  have hwv := sourceCovariantPartial_chart g hs hU hz w v
  rw [chartCoord_self] at hvw hwv
  rw [hvw, hwv]
  change fderiv ℝ (fun q => fderiv ℝ F q w) z v + _ =
    fderiv ℝ (fun q => fderiv ℝ F q v) z w + _
  rw [hpartial, hpartial,
    (hF.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])).eq v w,
    chartChristoffelContraction_symm g (U z) (fderiv ℝ F z v) (fderiv ℝ F z w)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sourceCovariantPartial_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sourceCovariantPartial_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sourceCovariantPartial_symm ``Submission.DifferentialGeometry.Geometry.sourceCovariantPartial_symm

end DifferentialGeometry.Geometry
