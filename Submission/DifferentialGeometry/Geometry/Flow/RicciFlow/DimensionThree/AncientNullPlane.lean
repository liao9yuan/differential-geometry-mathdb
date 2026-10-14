import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.TerminalLeastEigenvalue
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.LeastEigenvalueNullPlane

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem leastCurvatureOperatorEigenvalueAt_eq_zero_of_terminal_eq_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (hcarrier : D.carrier = _root_.Set.Iic 0) (hregular : D.regular = _root_.Set.Iio 0)
    (hR : ∀ t ≤ 0, ∀ x, metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M)
    (hzero : leastCurvatureOperatorEigenvalueAt (S.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric 0) x) = 0)
    {s : ℝ} (hs : s < 0) :
    leastCurvatureOperatorEigenvalueAt (S.base.metric s) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric s) x) = 0 := by
  have hnonneg :=
    (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
    (S.base.metric s) hdim).mpr (hR s hs.le x)
  apply le_antisymm _ hnonneg
  by_contra hnot
  have hpos : 0 < leastCurvatureOperatorEigenvalueAt (S.base.metric s) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric s) x) := lt_of_not_ge hnot
  let U := S.timeShift s
  have hU : IsSolutionOn U := isSolutionOn_timeShift hS s
  have hTU : 0 < -s := neg_pos.mpr hs
  have hcarrierU : (D.timeShift s).carrier = _root_.Set.Iic (-s) := by
    ext t
    simp only [RealTimeInterval.timeShift_carrier, _root_.Set.mem_ofPred_eq, hcarrier, _root_.Set.mem_Iic]
    constructor <;> intro h <;> linarith
  have hregularU : (D.timeShift s).regular = _root_.Set.Iio (-s) := by
    ext t
    simp only [RealTimeInterval.timeShift_regular, _root_.Set.mem_ofPred_eq, hregular, _root_.Set.mem_Iio]
    constructor <;> intro h <;> linarith
  have hRU : ∀ t ∈ _root_.Set.Icc 0 (-s), ∀ y : M,
      (⟨metricRm04At (U.base.metric t) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (U.base.metric t) y⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) y) ∈
            algebraicCurvatureOperatorNonnegativeCone := by
    intro t ht y
    exact hR (t + s) (by linarith [ht.2]) y
  have hposU : 0 < leastCurvatureOperatorEigenvalueAt (U.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (U.base.metric 0) x) := by
    simpa only [U, SolutionOn.timeShift_base_metric, zero_add] using hpos
  have hp := leastCurvatureOperatorEigenvalueAt_pos_at_terminal
    U hU hdim hTU hcarrierU hregularU hRU x hposU
  simp only [U, SolutionOn.timeShift_base_metric, neg_add_cancel, hzero,
    lt_self_iff_false] at hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.leastCurvatureOperatorEigenvalueAt_eq_zero_of_terminal_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.leastCurvatureOperatorEigenvalueAt_eq_zero_of_terminal_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.leastCurvatureOperatorEigenvalueAt_eq_zero_of_terminal_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.leastCurvatureOperatorEigenvalueAt_eq_zero_of_terminal_eq_zero

theorem exists_negative_time_null_plane_of_terminal_least_eigenvalue_eq_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (hcarrier : D.carrier = _root_.Set.Iic 0) (hregular : D.regular = _root_.Set.Iio 0)
    (hR : ∀ t ≤ 0, ∀ x, metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M)
    (hzero : leastCurvatureOperatorEigenvalueAt (S.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric 0) x) = 0)
    {s : ℝ} (hs : s < 0) :
    ∃ v w : TangentSpace I x,
      0 < (S.base.metric s).inner x v v * (S.base.metric s).inner x w w -
        ((S.base.metric s).inner x v w) ^ 2 ∧
      S.base.rm04 s x (vec4 v w w v) = 0 := by
  exact exists_null_plane_of_leastCurvatureOperatorEigenvalueAt_eq_zero
    (S.base.metric s) x hdim
    (leastCurvatureOperatorEigenvalueAt_eq_zero_of_terminal_eq_zero
      S hS hdim hcarrier hregular hR x hzero hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_negative_time_null_plane_of_terminal_least_eigenvalue_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_negative_time_null_plane_of_terminal_least_eigenvalue_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_negative_time_null_plane_of_terminal_least_eigenvalue_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_negative_time_null_plane_of_terminal_least_eigenvalue_eq_zero

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
