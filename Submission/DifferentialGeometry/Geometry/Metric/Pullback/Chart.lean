import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Retraction
import Submission.DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {V F E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem pullbackMetricCoefficients_fderiv_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {f : V → F} {ψ : F → M} {r : V → M} {x : V}
    (hf : DifferentiableAt ℝ f x)
    (hψ : MDifferentiableAt 𝓘(ℝ, F) I ψ (f x))
    (heq : ψ ∘ f =ᶠ[𝓝 x] r) (v w : V) :
    pullbackMetricCoefficients g ψ (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) =
      pullbackMetricCoefficients g r x v w := by
  have hd : (mfderiv 𝓘(ℝ, F) I ψ (f x) : F →L[ℝ] E).comp (fderiv ℝ f x) =
      (mfderiv 𝓘(ℝ, V) I r x : V →L[ℝ] E) := by
    have hc := mfderiv_comp x hψ hf.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hc
    exact hc.symm.trans heq.mfderiv_eq
  change (g.inner (ψ (f x)) : E →L[ℝ] E →L[ℝ] ℝ)
    (((mfderiv 𝓘(ℝ, F) I ψ (f x) : F →L[ℝ] E).comp (fderiv ℝ f x)) v)
    (((mfderiv 𝓘(ℝ, F) I ψ (f x) : F →L[ℝ] E).comp (fderiv ℝ f x)) w) = _
  rw [hd]
  change (g.inner (ψ (f x)) : E →L[ℝ] E →L[ℝ] ℝ)
    (mfderiv 𝓘(ℝ, V) I r x v) (mfderiv 𝓘(ℝ, V) I r x w) = _
  have hval : ψ (f x) = r x := heq.eq_of_nhds
  rw [hval]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eventuallyEq ``Submission.DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eventuallyEq

theorem pullbackMetricCoefficients_fderiv_of_eqOn
    (g : SmoothRiemannianMetric I M) {f : V → F} {ψ : F → M} {r : V → M}
    {W : Set V} (hW : IsOpen W) {x : V} (hx : x ∈ W)
    (hf : DifferentiableAt ℝ f x)
    (hψ : MDifferentiableAt 𝓘(ℝ, F) I ψ (f x))
    (heq : _root_.Set.EqOn (ψ ∘ f) r W) (v w : V) :
    pullbackMetricCoefficients g ψ (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) =
      pullbackMetricCoefficients g r x v w :=
  pullbackMetricCoefficients_fderiv_of_eventuallyEq g hf hψ
    (Filter.eventuallyEq_of_mem (hW.mem_nhds hx) heq) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eqOn ``Submission.DifferentialGeometry.Geometry.pullbackMetricCoefficients_fderiv_of_eqOn

section Chart

variable [FiniteDimensional ℝ E] [I.Boundaryless]

local notation "Eucl" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem pullbackMetricCoefficients_chart_fderiv
    (g : SmoothRiemannianMetric I M) (p : M)
    {r : V → M} {U : Set V} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) I ∞ r U) {x : V}
    (hx : x ∈ U ∩ r ⁻¹' (extChartAt I p).source) (v w : V) :
    let χ : V → Eucl := fun y => toEuclidean (extChartAt I p (r y))
    let ψ : Eucl → M := fun y => (extChartAt I p).symm ((toEuclidean (E := E)).symm y)
    pullbackMetricCoefficients g ψ (χ x) (fderiv ℝ χ x v) (fderiv ℝ χ x w) =
      pullbackMetricCoefficients g r x v w := by
  let chart := extChartAtPartialDiffeomorph I ∞ p
  let W : Set V := U ∩ r ⁻¹' chart.source
  let χ : V → Eucl := fun y => toEuclidean (chart (r y))
  let ψ : Eucl → M := fun y => chart.symm ((toEuclidean (E := E)).symm y)
  have hW : IsOpen W := hr.continuousOn.isOpen_inter_preimage hU chart.open_source
  have hχ : ContDiffOn ℝ ∞ χ W := by
    have hchart : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (chart ∘ r) W :=
      chart.contMDiffOn_toFun.comp (hr.mono _root_.Set.inter_subset_left) _root_.Set.inter_subset_right
    exact ((toEuclidean (E := E)).contDiff.contMDiff.comp_contMDiffOn hchart).contDiffOn
  have hχx : DifferentiableAt ℝ χ x :=
    (hχ.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have htarget : (toEuclidean (E := E)).symm (χ x) ∈ chart.target := by
    change (toEuclidean (E := E)).symm (toEuclidean (chart (r x))) ∈ chart.target
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact chart.toOpenPartialHomeomorph.map_source hx.2
  have hψ : MDifferentiableAt 𝓘(ℝ, Eucl) I ψ (χ x) :=
    ((chart.contMDiffOn_invFun.contMDiffAt (chart.open_target.mem_nhds htarget)).mdifferentiableAt
      (by simp)).comp (χ x) (toEuclidean (E := E)).symm.differentiableAt.mdifferentiableAt
  apply pullbackMetricCoefficients_fderiv_of_eqOn g hW hx hχx hψ
  intro y hy
  change chart.symm ((toEuclidean (E := E)).symm (toEuclidean (chart (r y)))) = r y
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact chart.toOpenPartialHomeomorph.left_inv hy.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.pullbackMetricCoefficients_chart_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.pullbackMetricCoefficients_chart_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.pullbackMetricCoefficients_chart_fderiv ``Submission.DifferentialGeometry.Geometry.pullbackMetricCoefficients_chart_fderiv

theorem pullbackMetricCoefficients_inverse_chart_of_leftInverse
    (g : SmoothRiemannianMetric I M) (p : M) {e : M → F} {r : F → M}
    (he : ContMDiff I 𝓘(ℝ, F) ∞ e) {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U) (heU : _root_.Set.range e ⊆ U)
    (hleft : Function.LeftInverse r e) {y : Eucl}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I p).target) (v w : Eucl) :
    let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
    let β : Eucl → F := e ∘ ψ
    pullbackMetricCoefficients g r (β y) (fderiv ℝ β y v) (fderiv ℝ β y w) =
      pullbackMetricCoefficients g ψ y v w := by
  let chart := extChartAtPartialDiffeomorph I ∞ p
  let ψ : Eucl → M := fun z => chart.symm ((toEuclidean (E := E)).symm z)
  have hψ : MDifferentiableAt 𝓘(ℝ, Eucl) I ψ y :=
    ((chart.contMDiffOn_invFun.contMDiffAt (chart.open_target.mem_nhds hy)).mdifferentiableAt
      (by simp)).comp y (toEuclidean (E := E)).symm.differentiableAt.mdifferentiableAt
  exact pullbackMetricCoefficients_comp_fderiv_of_leftInverse g
    (he.mdifferentiableAt (by simp))
    ((hr.contMDiffAt (hU.mem_nhds (heU (_root_.Set.mem_range_self (ψ y))))).mdifferentiableAt (by simp))
    hleft hψ v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.pullbackMetricCoefficients_inverse_chart_of_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.pullbackMetricCoefficients_inverse_chart_of_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.pullbackMetricCoefficients_inverse_chart_of_leftInverse ``Submission.DifferentialGeometry.Geometry.pullbackMetricCoefficients_inverse_chart_of_leftInverse

end Chart

end DifferentialGeometry.Geometry

end
