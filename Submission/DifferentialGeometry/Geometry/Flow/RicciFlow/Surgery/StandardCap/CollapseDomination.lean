import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseMap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionDomination
import Submission.DifferentialGeometry.Geometry.Measure.ProductLevel
import Submission.DifferentialGeometry.Geometry.Metric.WeakLength
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.MeasureTheory _root_.Filter _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Measure
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.InnerProductSpace _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal
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
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.EC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.EC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens (O : _root_.TopologicalSpace.Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpens (O : _root_.TopologicalSpace.Opens (S2 × ℝ)) : MeasurableSpace O := borel O

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpens target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceSubtypeProdElemE3S2RealMemOpens (O : _root_.TopologicalSpace.Opens (S2 × ℝ)) : BorelSpace O := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceSubtypeProdElemE3S2RealMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instBorelSpaceSubtypeProdElemE3S2RealMemOpens target :: scope.openDecls } }

private theorem radial_metric_bound (y : S2) (r s z : ℝ) (hr : 0 < r)
    (hs : s ∈ _root_.Set.Icc (0 : ℝ) 1) (v : TangentSpace IC (y, z)) :
    metric.inner (r • (y : E3))
      ((s * v.2) • (y : E3) + r • dIncl (n := 2) y v.1)
      ((s * v.2) • (y : E3) + r • dIncl (n := 2) y v.1) ≤
      (roundCylinderMetric (E := E3) (n := 2)).inner (y, z) v v := by
  rw [metric_inner_polar (norm_eq_of_mem_sphere y)
    (dIncl_orth y v.1) (dIncl_orth y v.1) hr, roundCylinderMetric_inner]
  have hi : 0 ≤ ⟪dIncl (n := 2) y v.1, dIncl (n := 2) y v.1⟫_ℝ := real_inner_self_nonneg
  have ha := warpingFunction_le_sqrt_two r
  have hp := (warpingFunction_pos hr).le
  have htwo : warpingFunction r ^ 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsquare : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  nlinarith [mul_nonneg (sub_nonneg.mpr htwo) hi,
    mul_nonneg (sub_nonneg.mpr hsquare) (sq_nonneg v.2)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_metric_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_metric_bound target :: scope.openDecls } }

private theorem collapseMap_deep_radius {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : q.val.2 ≤ -2 * A) :
    ‖(collapseMap hA hAB q : E3)‖ < conformalRadius (-7 * A / 4) := by
  change ‖collapseMapAmbient A q.val‖ < _
  rw [collapseMapAmbient_norm]
  apply max_lt
  · exact conformalRadius_pos _
  · calc
      collapseRadius A q.val.2 ≤ collapseRadius A (-2 * A) := monotone_collapseRadius A hq
      _ = conformalRadius (-2 * A) := collapseRadius_eq_conformalRadius le_rfl
      _ < conformalRadius (-7 * A / 4) := strictMono_conformalRadius (by linarith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_deep_radius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_deep_radius target :: scope.openDecls } }

private theorem collapseMap_deep_inner_le {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B)
    (htip : collapseTip A < q.val.2) (hq : q.val.2 ≤ -2 * A)
    (v : TangentSpace IC q) :
    (insertedMetric hA hAB hη h).inner (collapseMap hA hAB q)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v) ≤
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v := by
  rw [insertedMetric_inner_of_inner hA hAB hη h _ (collapseMap_deep_radius hA hAB q hq)]
  rw [collapseMap_mfderiv_of_tip_lt hA hAB q htip,
    collapseMap_radial hA hAB q htip.le]
  exact mul_le_mul_of_nonneg_left
    (radial_metric_bound q.val.1 (collapseRadius A q.val.2)
      (deriv (collapseRadius A) q.val.2) q.val.2 (collapseRadius_pos_iff.mpr htip)
      (deriv_collapseRadius_mem_Icc A q.val.2) v) hη.le

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_deep_inner_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_deep_inner_le target :: scope.openDecls } }

private theorem collapseMap_collar_mfderiv {A B : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (q : insertionCylinder A B)
    (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (collapseMap hA hAB)
      (Opens.inclusion (insertionCylinder_le_openCylinder hAB) q) v =
      mfderiv IC (𝓡 3) (insertionMap hA hAB) q v := by
  have htip := collapseTip_lt A
  have hL := transitionEnd_pos
  have hne : (Opens.inclusion (insertionCylinder_le_openCylinder hAB) q).val.2 ≠
      collapseTip A := by
    have hq := q.property.1
    change q.val.2 ≠ collapseTip A
    linarith
  have hcomp := congrArg (fun D => D v) (mfderiv_comp q
    ((contMDiffAt_collapseMap_of_height_ne hA hAB _ hne).mdifferentiableAt (by decide))
    ((contMDiff_inclusion (insertionCylinder_le_openCylinder hAB) (n := ∞)).mdifferentiable
      (by decide) q))
  have heq : collapseMap hA hAB ∘ Opens.inclusion (insertionCylinder_le_openCylinder hAB) =
      insertionMap hA hAB := funext (collapseMap_insertionMap hA hAB)
  rw [heq, mfderiv_opens_incl] at hcomp
  exact hcomp.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_collar_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_collar_mfderiv target :: scope.openDecls } }

theorem collapseMap_inner_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : DifferentialGeometry.Geometry.Neck.openCylinder B) (hq : q.val.2 ≠ collapseTip A)
    (v : TangentSpace IC q)
    (hlower : η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ h.inner q v v) :
    (insertedMetric hA hAB hη h).inner (collapseMap hA hAB q)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (collapseMap hA hAB) q v) ≤ h.inner q v v := by
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · rw [collapseMap_mfderiv_of_height_lt hA hAB q hlt]
    simpa using metric_inner_self_nonneg h q v
  · by_cases hdeep : q.val.2 ≤ -2 * A
    · exact (collapseMap_deep_inner_le hA hAB hη h q hgt hdeep v).trans hlower
    · let q' : insertionCylinder A B := ⟨q.val, not_le.mp hdeep, q.property.2⟩
      have hq' : Opens.inclusion (insertionCylinder_le_openCylinder hAB) q' = q := Subtype.ext rfl
      have heq := collapseMap_insertionMap hA hAB q'
      rw [hq'] at heq
      have hd : mfderiv IC (𝓡 3) (collapseMap hA hAB) q v =
          mfderiv IC (𝓡 3) (insertionMap hA hAB) q' v := by
        simpa only [hq'] using! collapseMap_collar_mfderiv hA hAB q' v
      erw [heq, hd]
      exact insertedMetric_inner_le_of_cylinder_lower hA hAB hη h q' v hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_inner_le_of_cylinder_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_inner_le_of_cylinder_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_inner_le_of_cylinder_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_inner_le_of_cylinder_lower

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem collapseMap_eVariationOn_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (hlower : ∀ q : DifferentialGeometry.Geometry.Neck.openCylinder B, ∀ v : TangentSpace IC q,
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ g.inner q v v)
    (γ : ℝ → DifferentialGeometry.Geometry.Neck.openCylinder B) (a b : ℝ)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    (let cg := g.toContinuousRiemannianMetric
     letI : _root_.Bundle.RiemannianBundle (TangentSpace IC : DifferentialGeometry.Geometry.Neck.openCylinder B → Type _) :=
       ⟨cg.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle EC
       (TangentSpace IC : DifferentialGeometry.Geometry.Neck.openCylinder B → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (DifferentialGeometry.Geometry.Neck.openCylinder B) :=
       .ofRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)
     let k := insertedMetric hA hAB hη g
     let ck := k.toContinuousRiemannianMetric
     letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : insertionBall B → Type _) :=
       ⟨ck.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall B → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (insertionBall B) := .ofRiemannianMetric (𝓡 3) (insertionBall B)
     eVariationOn (collapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) ≤ eVariationOn γ (_root_.Set.Icc a b)) := by
  apply eVariationOn_comp_le_of_ae_mfderiv g (insertedMetric hA hAB hη g)
    (collapseMap hA hAB) (collapseMap_local_intrinsic_bound hA hAB g _) _ γ a b hγ
  have hnull := riemannianVolumeMeasure_snd_fiber_eq_zero
    (DifferentialGeometry.Geometry.Neck.openCylinder B) g (collapseTip A)
  have hae : ∀ᵐ q ∂riemannianVolumeMeasure IC (DifferentialGeometry.Geometry.Neck.openCylinder B) g,
      q.val.2 ≠ collapseTip A := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with q hq
  intro _hdiff v
  exact Real.sqrt_le_sqrt (collapseMap_inner_le_of_cylinder_lower hA hAB hη g q hq v (hlower q v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_eVariationOn_le_of_cylinder_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_eVariationOn_le_of_cylinder_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_eVariationOn_le_of_cylinder_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_eVariationOn_le_of_cylinder_lower

end DifferentialGeometry.PDE.RicciFlow.StandardCap
