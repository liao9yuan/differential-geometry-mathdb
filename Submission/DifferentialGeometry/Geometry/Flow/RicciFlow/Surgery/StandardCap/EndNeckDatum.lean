import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Polar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import Submission.DifferentialGeometry.Geometry.Neck.NormalizedDatum
import Submission.DifferentialGeometry.Geometry.Metric.CylinderAxial
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }
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
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3OfNat : Fact (Module.finrank ℝ E3 = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3OfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3OfNat target :: scope.openDecls } }

private def shift (r δ : ℝ) : bufferedCylinder δ → S2 × ℝ :=
  fun q => cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num) q.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.shift target :: scope.openDecls } }
private theorem shift_smooth (r δ : ℝ) : ContMDiff IC IC ∞ (shift r δ) :=
  (cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num)).contMDiff.comp contMDiff_subtype_val

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.shift_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.shift_smooth target :: scope.openDecls } }
private theorem shift_derivative (r δ : ℝ) (q : bufferedCylinder δ)
    (v : TangentSpace IC q) : mfderiv IC IC (shift r δ) q v = v := by
  have h := congrArg (fun D => D v) (mfderiv_comp q
    ((cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num)).contMDiff.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q.val)
    ((contMDiff_subtype_val (I := IC) (U := bufferedCylinder δ)).mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q))
  change mfderiv IC IC (shift r δ) q v = _ at h
  rw [ContinuousLinearMap.comp_apply, mfderiv_subtype_val] at h
  rw [cylinderAxialDiffeomorph_mfderiv] at h
  change mfderiv IC IC (shift r δ) q v = (v.1, 1 * v.2) at h
  exact h.trans (by change (v.1, 1 * v.2) = v; rw [one_mul]; rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.shift_derivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.shift_derivative target :: scope.openDecls } }
private theorem shift_end {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : transitionEnd < (shift r δ q).2 := by
  change transitionEnd < r + 1 * q.val.2
  have hq := q.property.1
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.shift_end
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.shift_end target :: scope.openDecls } }

def endNeckMap (r δ : ℝ) (q : bufferedCylinder δ) : E3 := euclideanPolarMap (shift r δ q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap

theorem endNeckMap_apply (r δ : ℝ) (q : bufferedCylinder δ) :
    endNeckMap r δ q = (r + q.val.2) • (q.val.1 : E3) := by
  simp only [endNeckMap, euclideanPolarMap, shift, cylinderAxialDiffeomorph_apply, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_apply

private theorem end_smooth (r δ : ℝ) : ContMDiff IC (𝓡 3) ∞ (endNeckMap r δ) :=
  euclideanPolarMap_smooth.comp (shift_smooth r δ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.end_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.end_smooth target :: scope.openDecls } }
private theorem end_derivative (r δ : ℝ) (q : bufferedCylinder δ) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (endNeckMap r δ) q v =
      mfderiv IC (𝓡 3) euclideanPolarMap (shift r δ q) v := by
  have h := congrArg (fun D => D v) (mfderiv_comp q
    (euclideanPolarMap_smooth.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) (shift r δ q))
    ((shift_smooth r δ).mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q))
  change mfderiv IC (𝓡 3) (endNeckMap r δ) q v = _ at h
  rw [ContinuousLinearMap.comp_apply, shift_derivative] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.end_derivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.end_derivative target :: scope.openDecls } }
private theorem end_injective {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r) :
    Injective (endNeckMap r δ) := by
  intro q q' h
  have hs := euclideanPolarMap_injOn (transitionEnd_pos.trans (shift_end hr q))
    (transitionEnd_pos.trans (shift_end hr q')) h
  exact Subtype.val_injective
    ((cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num)).injective hs)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.end_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.end_injective target :: scope.openDecls } }
private theorem end_immersion {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : _root_.Function.Injective (mfderiv IC (𝓡 3) (endNeckMap r δ) q) := by
  have hp := PartialDiffeomorph.isLocalDiffeomorphAt IC (𝓡 3) ∞
    (euclideanPolarDiffeomorph (n := 2))
    (transitionEnd_pos.trans (shift_end hr q))
  intro v w h
  rw [end_derivative, end_derivative] at h
  exact (hp.mfderivToContinuousLinearEquiv (by simp)).injective h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.end_immersion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.end_immersion target :: scope.openDecls } }

theorem endNeckMap_norm {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : ‖endNeckMap r δ q‖ = r + q.val.2 := by
  exact (euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans (shift_end hr q))).trans
    (by simp only [shift, cylinderAxialDiffeomorph_apply, one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_norm

theorem endNeckMap_scalar {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : metricScalarAt metric (endNeckMap r δ q) = 1 := by
  apply metricScalarAt_cylindrical
  change transitionEnd ≤ ‖euclideanPolarMap (shift r δ q)‖
  rw [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans (shift_end hr q))]
  exact (shift_end hr q).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckMap_scalar

private theorem end_tensor {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) (v w : TangentSpace IC q) :
    metric.inner (endNeckMap r δ q)
      (mfderiv IC (𝓡 3) (endNeckMap r δ) q v)
    (mfderiv IC (𝓡 3) (endNeckMap r δ) q w) = (referenceMetric δ).inner q v w := by
  rw [end_derivative, end_derivative]
  rw [endNeckMap, referenceMetric, SmoothRiemannianMetric.restrictOpen_inner]
  let gS := scaleMetric 2 (by norm_num)
    (DifferentialGeometry.Geometry.roundMetric (E := E3) (n := 2))
  have hmetric := congrArg
    (fun g : SmoothRiemannianMetric IC (S2 × ℝ) => g.inner (q : S2 × ℝ) v w)
    (pullback_cylinderMetric_cylinderAxialDiffeomorph gS r 1 (by norm_num))
  have hpull := Diffeomorph.pullbackMetric_inner (cylinderMetric gS)
    (cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num))
    (q : S2 × ℝ) v w
  have htransport := hpull.symm.trans hmetric
  have hdv := cylinderAxialDiffeomorph_mfderiv
    (I := 𝓡 2) r 1 (by norm_num) (q : S2 × ℝ) v
  have hdw := cylinderAxialDiffeomorph_mfderiv
    (I := 𝓡 2) r 1 (by norm_num) (q : S2 × ℝ) w
  rw [hdv, hdw] at htransport
  simp only [one_mul] at htransport
  have hv : (v.1, v.2) = v := rfl
  have hw : (w.1, w.2) = w := rfl
  rw [hv, hw] at htransport
  have hgS : cylinderMetric gS = roundCylinderMetric (E := E3) (n := 2) := by
    rfl
  have hshift :
      cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num) (q : S2 × ℝ) =
        shift r δ q := by
    rfl
  rw [hgS, hshift] at htransport
  have htransport' :
      (roundCylinderMetric (E := E3) (n := 2)).inner (shift r δ q) v w =
        (roundCylinderMetric (E := E3) (n := 2)).inner (q : S2 × ℝ) v w := by
    exact htransport
  exact (metric_polar_pullback_cylindrical
    (shift r δ q) (shift_end hr q).le v w).trans htransport'

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.end_tensor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.end_tensor target :: scope.openDecls } }

def endNeckDatum (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    normalizedDatum metric (r • (spherePoint : E3)) δ k := by
  have hc : endNeckMap r δ (cylinderCenter δ hδ) = r • (spherePoint : E3) := by
    rw [endNeckMap_apply]; simp only [cylinderCenter, add_zero]
  have hscalar : metricScalarAt metric (r • (spherePoint : E3)) = 1 := by
    rw [← hc]; exact endNeckMap_scalar hr _
  have hp : 0 < metricScalarAt metric (r • (spherePoint : E3)) := by rw [hscalar]; norm_num
  have hloc := isLocalDiffeomorph_of_injective_mfderiv (endNeckMap r δ) (end_smooth r δ)
    (end_immersion hr) (by simp)
  have he : pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hp metric)
      (endNeckMap r δ) hloc (end_injective hr) = referenceMetric δ := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, hscalar, one_mul]
    exact end_tensor hr q v w
  refine
    { precision_pos := hδ
      precision_lt_one := hδ1
      map := endNeckMap r δ
      smooth := end_smooth r δ
      injective := end_injective hr
      immersion := end_immersion hr
      center_eq := hc
      scalar_pos := hp
      retainedSide := side
      error_lt := ?_ }
  change metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hp metric)
      (endNeckMap r δ) hloc (end_injective hr)) (referenceMetric δ) (referenceMetric δ) < _
  rw [he, metricDerivENormSupOn_self]
  exact ENNReal.ofReal_pos.mpr hδ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum

theorem endNeckDatum_map (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    (endNeckDatum r δ hδ hδ1 hr k side).map = endNeckMap r δ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_map ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_map

theorem endNeckDatum_normalizedMetric (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    (endNeckDatum r δ hδ hδ1 hr k side).normalizedMetric = referenceMetric δ := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [normalizedDatum.normalizedMetric_inner]
  have hc : endNeckMap r δ (cylinderCenter δ hδ) = r • (spherePoint : E3) := by
    rw [endNeckMap_apply]; simp only [cylinderCenter, add_zero]
  have hscalar : metricScalarAt metric (r • (spherePoint : E3)) = 1 := by
    rw [← hc]; exact endNeckMap_scalar hr _
  rw [hscalar, one_mul]
  exact end_tensor hr q v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_normalizedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_normalizedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_normalizedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_normalizedMetric

theorem endNeckDatum_retainedSide (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    (endNeckDatum r δ hδ hδ1 hr k side).retainedSide = side := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_retainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_retainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_retainedSide ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.endNeckDatum_retainedSide
end DifferentialGeometry.PDE.RicciFlow.StandardCap
