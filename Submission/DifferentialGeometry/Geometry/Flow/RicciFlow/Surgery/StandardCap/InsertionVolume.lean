import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionNorm
import Submission.DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import Submission.DifferentialGeometry.Geometry.Measure.MetricComparison
import Submission.DifferentialGeometry.Geometry.Measure.OpenRestriction
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3 : MeasurableSpace E3 := borel E3

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3 : BorelSpace E3 := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceSubtypeE3MemOpens (U : _root_.TopologicalSpace.Opens E3) : MeasurableSpace U := borel U

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceSubtypeE3MemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceSubtypeE3MemOpens target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceSubtypeE3MemOpens (U : _root_.TopologicalSpace.Opens E3) : BorelSpace U := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceSubtypeE3MemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceSubtypeE3MemOpens target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instLocallyCompactSpaceSubtypeE3MemOpens (U : _root_.TopologicalSpace.Opens E3) : LocallyCompactSpace U := U.isOpen.locallyCompactSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instLocallyCompactSpaceSubtypeE3MemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instLocallyCompactSpaceSubtypeE3MemOpens target :: scope.openDecls } }

private theorem cap_volume_le_two_of_error_lt {B : ℝ} (hB : 0 < B)
    (g : SmoothRiemannianMetric (𝓡 3) (insertionBall B))
    (herr : metricDerivENormSupOn {x : insertionBall B | ‖(x : E3)‖ ≤ transitionEnd} 0 g
      (metric.restrictOpen (insertionBall B)) (metric.restrictOpen (insertionBall B)) <
      ENNReal.ofReal (1 / 2 : ℝ)) :
    riemannianVolumeMeasure (𝓡 3) (insertionBall B) g {x | ‖(x : E3)‖ ≤ transitionEnd} ≤
      2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
  have hcomp (x : insertionBall B) (hx : ‖(x : E3)‖ ≤ transitionEnd) (v : TangentSpace (𝓡 3) x) :
      g.inner x v v ≤ (3 / 2 : ℝ) * (metric.restrictOpen (insertionBall B)).inner x v v := by
    have h := (inner_bounds_of_metricDerivENormSupOn_lt
      (metric.restrictOpen (insertionBall B)) g herr hx v).2
    norm_num only [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at h
    exact h
  have hmeas : MeasurableSet {x : insertionBall B | ‖(x : E3)‖ ≤ transitionEnd} :=
    (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const).measurableSet
  have hv := riemannianVolumeMeasure_apply_le_of_inner_le
    (metric.restrictOpen (insertionBall B)) g (C := 3 / 2) (by norm_num) hmeas hcomp
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim] at hv
  have hrestriction := riemannianVolumeMeasure_restrictOpen_preimage metric (insertionBall B)
    (K := {x : E3 | ‖x‖ ≤ transitionEnd})
    ((isClosed_le continuous_norm continuous_const).measurableSet)
    (by intro x hx; change ‖x‖ < transitionEnd + B; change ‖x‖ ≤ transitionEnd at hx; linarith)
  have hfactor : ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) ≤ 2 := by
    have hs : Real.sqrt ((3 / 2 : ℝ) ^ 3) < 2 :=
      (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
    exact (ENNReal.ofReal_le_ofReal hs.le).trans_eq (by norm_num)
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) *
        riemannianVolumeMeasure (𝓡 3) (insertionBall B) (metric.restrictOpen (insertionBall B))
          {x | ‖(x : E3)‖ ≤ transitionEnd} := hv
    _ = ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) *
        riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
          exact congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal (Real.sqrt ((3 / 2 : ℝ) ^ 3)) * t) hrestriction
    _ ≤ _ := mul_le_mul' hfactor le_rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_le_two_of_error_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_volume_le_two_of_error_lt target :: scope.openDecls } }

theorem exists_insertedMetric_cap_volume_bound (A : ℝ) (hA : 0 < A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (B : ℝ) (hAB : 2 * A < B), 1 < B →
      ∀ (η : ℝ) (hη : 0 < η)
        (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
        metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ _root_.Set.Icc (-2 * A) 0} 0 h
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) +
          ENNReal.ofReal |η - 1| < ENNReal.ofReal ε →
        riemannianVolumeMeasure (𝓡 3) (insertionBall B) (insertedMetric hA hAB hη h)
          {x | ‖(x : E3)‖ ≤ transitionEnd} ≤
          2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} := by
  obtain ⟨C, hC, hb⟩ := exists_insertedMetric_ball_error_bound A hA 0 (by norm_num) 0
  let ε := (2 * C)⁻¹
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, ?_⟩
  intro B hAB hB η hη h hin
  apply cap_volume_le_two_of_error_lt (by linarith : 0 < B) (insertedMetric hA hAB hη h)
  have hbound := hb B hAB (by simpa using hB) η hη h
  simp only [add_zero] at hbound
  apply hbound.trans_lt
  have hm := ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top hin
  have he : C * ε = 1 / 2 := by dsimp [ε]; field_simp
  rw [← ENNReal.ofReal_mul hC.le, he] at hm
  exact hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_cap_volume_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_cap_volume_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_cap_volume_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_cap_volume_bound

theorem exists_insertedMetric_scaled_cap_volume_bound (A : ℝ) (hA : 0 < A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (B : ℝ) (hAB : 2 * A < B), 1 < B →
      ∀ (η : ℝ) (hη : 0 < η)
        (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
        metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ _root_.Set.Icc (-2 * A) 0} 0 h
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) +
          ENNReal.ofReal |η - 1| < ENNReal.ofReal ε →
        ∀ (Q : ℝ) (hQ : 0 < Q),
          riemannianVolumeMeasure (𝓡 3) (insertionBall B)
            (scaleMetric Q⁻¹ (inv_pos.mpr hQ) (insertedMetric hA hAB hη h))
            {x | ‖(x : E3)‖ ≤ transitionEnd} ≤
            ENNReal.ofReal (Real.sqrt Q⁻¹) ^ 3 *
              (2 * riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}) := by
  obtain ⟨ε, hε, hb⟩ := exists_insertedMetric_cap_volume_bound A hA
  refine ⟨ε, hε, ?_⟩
  intro B hAB hB η hη h hin Q hQ
  rw [volume_scale_apply]
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim]
  exact mul_le_mul' le_rfl (hb B hAB hB η hη h hin)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_scaled_cap_volume_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_scaled_cap_volume_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_scaled_cap_volume_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_insertedMetric_scaled_cap_volume_bound

end DifferentialGeometry.PDE.RicciFlow.StandardCap
