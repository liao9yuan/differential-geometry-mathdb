import Submission.DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Basic
import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Frame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

noncomputable def framedExpMap (g : SmoothRiemannianMetric I M) (p : M) :
    E -> M :=
  fun z => expMap (I := I) g p (normalFrame (I := I) g p z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] in
@[simp] theorem framedExpMap_apply (g : SmoothRiemannianMetric I M) (p : M)
    (z : E) :
    framedExpMap (I := I) g p z =
      expMap (I := I) g p (normalFrame (I := I) g p z) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpMap_apply

noncomputable def framedExpDiffeo (g : SmoothRiemannianMetric I M) (p : M) :
    PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1 := by
  let Φ := expMapDiffeo (I := I) g p
  let L : E ≃L[Real] E :=
    (normalFrame (I := I) g p).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) p)
  exact
    { toPartialEquiv :=
        { toFun := fun z => Φ (L z)
          invFun := fun q => L.symm (Φ.symm q)
          source := L ⁻¹' Φ.source
          target := Φ.target
          map_source' := by
            intro z hz
            exact Φ.map_source hz
          map_target' := by
            intro q hq
            change L (L.symm (Φ.symm q)) ∈ Φ.source
            rw [L.apply_symm_apply]
            exact Φ.map_target hq
          left_inv' := by
            intro z hz
            calc
              L.symm (Φ.symm (Φ (L z))) = L.symm (L z) :=
                congrArg L.symm (Φ.left_inv hz)
              _ = z := L.symm_apply_apply z
          right_inv' := by
            intro q hq
            rw [L.apply_symm_apply]
            exact Φ.right_inv hq }
      open_source := Φ.open_source.preimage L.continuous
      open_target := Φ.open_target
      contMDiffOn_toFun :=
        Φ.contMDiffOn_toFun.comp
          L.toContinuousLinearMap.contMDiff.contMDiffOn (fun _ hz => hz)
      contMDiffOn_invFun :=
        L.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
          Φ.contMDiffOn_invFun }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpDiffeo ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExpDiffeo

noncomputable def framedChartAt (g : SmoothRiemannianMetric I M) (p : M) :
    PartialDiffeomorph I (modelWithCornersSelf Real E) M E 1 :=
  (framedExpDiffeo (I := I) g p).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChartAt ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChartAt

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedExp_source (g : SmoothRiemannianMetric I M) (p : M) :
    (framedExpDiffeo (I := I) g p).source =
      (fun z => tangentSpaceModelContinuousLinearEquiv (I := I) p
        (normalFrame (I := I) g p z)) ⁻¹'
        (expMapDiffeo (I := I) g p).source := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_source ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_source

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedExp_target (g : SmoothRiemannianMetric I M) (p : M) :
    (framedExpDiffeo (I := I) g p).target =
      (expMapDiffeo (I := I) g p).target := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_target ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_target

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedExp_apply (g : SmoothRiemannianMetric I M) (p : M)
    (z : E) :
    framedExpDiffeo (I := I) g p z =
      expMapDiffeo (I := I) g p
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p z)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_apply

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] in
theorem framed_norm_lt_iff (g : SmoothRiemannianMetric I M) (p : M)
    (z : E) (r : Real) :
    Real.sqrt
        (g.inner p (normalFrame (I := I) g p z)
          (normalFrame (I := I) g p z)) < r ↔
      z ∈ Metric.ball (0 : E) r := by
  rw [normalFrame_sqrt, Metric.mem_ball, dist_zero_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framed_norm_lt_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framed_norm_lt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framed_norm_lt_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framed_norm_lt_iff

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedChart_apply (g : SmoothRiemannianMetric I M) (p : M)
    (q : M) :
    framedChartAt (I := I) g p q =
      (normalFrame (I := I) g p).symm
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm
          (normalChartAt (I := I) g p q)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_apply

omit [NeZero (Module.finrank Real E)] in
theorem zero_mem_framedExp_source (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ (framedExpDiffeo (I := I) g p).source := by
  rw [framedExp_source]
  change tangentSpaceModelContinuousLinearEquiv (I := I) p
      (normalFrame (I := I) g p 0) ∈ (expMapDiffeo (I := I) g p).source
  rw [map_zero, map_zero]
  exact zero_mem_expMapDiffeo_source (I := I) g p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.zero_mem_framedExp_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.zero_mem_framedExp_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.zero_mem_framedExp_source ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.zero_mem_framedExp_source

omit [NeZero (Module.finrank Real E)] in
theorem framedExp_zero (g : SmoothRiemannianMetric I M) (p : M) :
    framedExpDiffeo (I := I) g p (0 : E) = p := by
  rw [framedExp_apply, map_zero]
  exact expMapDiffeo_zero (I := I) g p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_zero

omit [NeZero (Module.finrank Real E)] in
theorem framedChart_centre (g : SmoothRiemannianMetric I M) (p : M) :
    framedChartAt (I := I) g p p = (0 : E) := by
  rw [framedChart_apply, normalChartAt_centre]
  rw [map_zero, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_centre then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_centre"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_centre ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedChart_centre

noncomputable def framedTransition (g : SmoothRiemannianMetric I M) (p q : M) :
    E -> E :=
  fun z => framedChartAt (I := I) g q (framedExpDiffeo (I := I) g p z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTransition ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTransition

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedTrans_apply (g : SmoothRiemannianMetric I M) (p q : M)
    (z : E) :
    framedTransition (I := I) g p q z =
      framedChartAt (I := I) g q (framedExpDiffeo (I := I) g p z) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTrans_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTrans_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTrans_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedTrans_apply

omit [NeZero (Module.finrank Real E)] in
theorem framedExp_eq_expMap (g : SmoothRiemannianMetric I M) (p : M)
    {z : E} (hz : z ∈ (framedExpDiffeo (I := I) g p).source) :
    framedExpDiffeo (I := I) g p z =
      framedExpMap (I := I) g p z := by
  rw [framedExpMap_apply, framedExp_apply]
  rw [expMapDiffeo_apply_eq (I := I) g p (by
    rw [framedExp_source] at hz
    exact hz)]
  exact congrArg (expMap (I := I) g p)
    (tangentSpaceModelContinuousLinearEquiv_apply (I := I) p
      (normalFrame (I := I) g p z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_eq_expMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_eq_expMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_eq_expMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedExp_eq_expMap

omit [NeZero (Module.finrank Real E)] in
theorem mfderiv_framedExp (g : SmoothRiemannianMetric I M) (p : M)
    {z : E} (hz : z ∈ (framedExpDiffeo (I := I) g p).source) :
    mfderiv (modelWithCornersSelf Real E) I
        (fun w : E => framedExpDiffeo (I := I) g p w) z =
      (mfderiv (modelWithCornersSelf Real E) I
        (fun u : E => expMapDiffeo (I := I) g p u)
        (tangentSpaceModelContinuousLinearEquiv (I := I) p
          (normalFrame (I := I) g p z))).comp
          ((tangentSpaceModelContinuousLinearEquiv (I := I) p).toContinuousLinearMap.comp
            (normalFrame (I := I) g p).toContinuousLinearMap) := by
  let Φ := expMapDiffeo (I := I) g p
  let L : E ≃L[Real] E :=
    (normalFrame (I := I) g p).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) p)
  let L0 : E →L[Real] E := L.toContinuousLinearMap
  have hzraw : L0 z ∈ Φ.source := by
    rw [framedExp_source] at hz
    exact hz
  have hΦ : MDifferentiableAt (modelWithCornersSelf Real E) I
      (fun u : E => Φ u) (L0 z) :=
    Φ.mdifferentiableAt one_ne_zero hzraw
  have hL : MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun w : E => L0 w) z :=
    L0.contMDiff.mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp (I := modelWithCornersSelf Real E)
    (I' := modelWithCornersSelf Real E) (I'' := I) z hΦ hL
  have hLderiv : mfderiv (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun w : E => L0 w) z = L0 := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rw [hLderiv] at hchain
  have hfun : (fun w : E => framedExpDiffeo (I := I) g p w) =
      fun w : E => Φ (L0 w) := by
    funext w
    exact framedExp_apply (I := I) g p w
  rw [hfun]
  change @Eq (E →L[Real] E) _ _ at hchain ⊢
  change @Eq (E →L[Real] E)
    (mfderiv (modelWithCornersSelf Real E) I (fun w : E => Φ (L0 w)) z)
    ((mfderiv (modelWithCornersSelf Real E) I (fun u : E => Φ u) (L0 z)).comp L0)
      at hchain ⊢
  exact hchain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExp ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExp

noncomputable def framedMetric (g : SmoothRiemannianMetric I M) (p : M) :
    E -> E →L[Real] E →L[Real] Real :=
  fun z =>
    let D : E →L[Real] TangentSpace I (framedExpDiffeo (I := I) g p z) :=
      mfderiv (modelWithCornersSelf Real E) I
        (fun w : E => framedExpDiffeo (I := I) g p w) z
    (ContinuousLinearMap.precomp Real D).comp
      ((g.inner (framedExpDiffeo (I := I) g p z)).comp D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric

omit [NeZero (Module.finrank Real E)] in
theorem framedMetric_apply (g : SmoothRiemannianMetric I M) (p : M)
    (z v w : E) :
    framedMetric (I := I) g p z v w =
      g.inner (framedExpDiffeo (I := I) g p z)
        (mfderiv (modelWithCornersSelf Real E) I
          (fun q : E => framedExpDiffeo (I := I) g p q) z v)
        (mfderiv (modelWithCornersSelf Real E) I
          (fun q : E => framedExpDiffeo (I := I) g p q) z w) := by
  simp only [framedMetric, ContinuousLinearMap.comp_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_apply

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem framedMetric_zero (g : SmoothRiemannianMetric I M) (p : M) :
    framedMetric (I := I) g p 0 =
      (innerSL Real : E →L[Real] E →L[Real] Real) := by
  ext v w
  rw [framedMetric_apply, framedExp_zero,
    mfderiv_framedExp (I := I) g p (zero_mem_framedExp_source (I := I) g p),
    map_zero]
  calc
    g.inner p
        (mfderiv (modelWithCornersSelf Real E) I
          (fun u : E => expMapDiffeo (I := I) g p u) 0
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p v)))
        (mfderiv (modelWithCornersSelf Real E) I
          (fun u : E => expMapDiffeo (I := I) g p u) 0
          (tangentSpaceModelContinuousLinearEquiv (I := I) p
            (normalFrame (I := I) g p w))) =
      g.inner p (normalFrame (I := I) g p v)
        (normalFrame (I := I) g p w) :=
      by
        change g.inner p
            (mfderiv (modelWithCornersSelf Real E) I
              (normalChartAt (I := I) g p).symm 0
              (tangentSpaceModelContinuousLinearEquiv (I := I) p
                (normalFrame (I := I) g p v)))
            (mfderiv (modelWithCornersSelf Real E) I
              (normalChartAt (I := I) g p).symm 0
              (tangentSpaceModelContinuousLinearEquiv (I := I) p
                (normalFrame (I := I) g p w))) = _
        simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using
          normalChartAt_metric_pullback_at_origin (I := I) g p
            (tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p v))
            (tangentSpaceModelContinuousLinearEquiv (I := I) p
              (normalFrame (I := I) g p w))
    _ = Inner.inner Real v w := normalFrame_inner (I := I) g p v w
    _ = (innerSL Real : E →L[Real] E →L[Real] Real) v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.framedMetric_zero

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
