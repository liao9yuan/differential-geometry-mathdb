import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Analysis.Integration.L2.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

namespace SmoothCcTensor


theorem hasCompactSupport_toFun
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) : HasCompactSupport S.toFun :=
  S.hasCompactSupport

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_toFun ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_toFun


theorem hasCompactSupport_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    HasCompactSupport
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (S.toFun x)) := by
  refine HasCompactSupport.mono (f := S.toFun) S.hasCompactSupport ?_
  intro x hx
  by_contra hSx
  apply hx
  have hSx_zero : S.toFun x = 0 := by simpa using hSx
  change tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (S.toFun x) = 0
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_self ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_self


theorem hasCompactSupport_inner_cross
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    HasCompactSupport
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (T.toFun x)) := by
  refine HasCompactSupport.mono (f := S.toFun) S.hasCompactSupport ?_
  intro x hx
  by_contra hSx
  apply hx
  have hSx_zero : S.toFun x = 0 := by simpa using hSx
  change tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (T.toFun x) = 0
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x (T.toFun x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_cross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_cross ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.hasCompactSupport_inner_cross

private lemma rs_baseSet_eq_chart_source (α : M) (r s : ℕ) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet =
      (chartAt H α).source := by
  change ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) α).baseSet) =
        (chartAt H α).source
  change (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ∩
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.rs_baseSet_eq_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.rs_baseSet_eq_chart_source target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma tangent_baseSet_eq_chart_source (α : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tangent_baseSet_eq_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tangent_baseSet_eq_chart_source target :: scope.openDecls } }

private lemma contMDiffOn_trivProj_chart_source
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) := by
  have hbase := rs_baseSet_eq_chart_source (E := E) (I := I) (M := M) α r s
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := _root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  exact hrewrite

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.contMDiffOn_trivProj_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.contMDiffOn_trivProj_chart_source target :: scope.openDecls } }

private lemma continuousOn_trivProj_chart_source
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (fun x : M => (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) :=
  (contMDiffOn_trivProj_chart_source (I := I) (M := M) S α).continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.continuousOn_trivProj_chart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.continuousOn_trivProj_chart_source target :: scope.openDecls } }

private lemma continuous_totalSpace_section
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    Continuous
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
  S.toSection.contMDiff.continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_totalSpace_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_totalSpace_section target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma tangent_continuousLinearMapAt_self (x : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (b₀ := x) (b := x) (mem_chart_source H x)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tangent_continuousLinearMapAt_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tangent_continuousLinearMapAt_self target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma tangent_symmL_self (x : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symmL ℝ x = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (b₀ := x) (b := x) (mem_chart_source H x)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tangent_symmL_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tangent_symmL_self target :: scope.openDecls } }

private lemma tensor0S_continuousLinearMapAt_self_apply (s : ℕ) (x : M)
    (p : Tensor0SSpace s I x) :
    (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).continuousLinearMapAt ℝ x p = p := by
  have hx_base : x ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hcLMAt :
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).continuousLinearMapAt ℝ x p =
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x ⟨x, p⟩).2 := by
    change (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).linearMapAt ℝ x p = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  rw [hcLMAt]
  have happly : (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x ⟨x, p⟩).2 =
      p.compContinuousLinearMap
        (fun _ => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symmL ℝ x) := rfl
  rw [happly, tangent_symmL_self (I := I) (M := M) x]
  ext v
  change p (fun i => (1 : E →L[ℝ] E) (v i)) = p v
  congr

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor0S_continuousLinearMapAt_self_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor0S_continuousLinearMapAt_self_apply target :: scope.openDecls } }

private lemma tensor0S_symmL_self_apply (s : ℕ) (x : M)
    (p : Tensor0SModel s ℝ E) :
    (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).symmL ℝ x p = p := by
  have hbase : x ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hinv : (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) x).continuousLinearMapAt ℝ x
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).symmL ℝ x p) = p :=
    Bundle.Trivialization.continuousLinearMapAt_symmL
      (R := ℝ) (e := _root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x) hbase p
  have hid := tensor0S_continuousLinearMapAt_self_apply (I := I) (M := M) s x
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) x).symmL ℝ x p)
  exact hid.symm.trans hinv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor0S_symmL_self_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tensor0S_symmL_self_apply target :: scope.openDecls } }

private lemma tensorRS_centre_point_identity
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (x : M) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) x ⟨x, S.toSection x⟩).2 = S.toFun x := by
  have heq :
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) x ⟨x, S.toSection x⟩).2 =
      ContinuousLinearMap.inCoordinates (Tensor0SModel r ℝ E) (Tensor0SSpace r I)
        (Tensor0SModel s ℝ E) (Tensor0SSpace s I) x x x x (S.toSection x) := by
    rfl
  rw [heq]
  ext v
  unfold ContinuousLinearMap.inCoordinates
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [tensor0S_symmL_self_apply (I := I) (M := M) r x v]
  rw [tensor0S_continuousLinearMapAt_self_apply (I := I) (M := M) s x
    ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x) v)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.tensorRS_centre_point_identity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.tensorRS_centre_point_identity target :: scope.openDecls } }

private lemma inner_self_eq_zero_off_support
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s)
    {x : M} (hx : x ∉ tsupport S.toFun) :
    tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (S.toFun x) = 0 := by
  have hSx_zero : S.toFun x = 0 := by
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_self_eq_zero_off_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_self_eq_zero_off_support target :: scope.openDecls } }

private lemma inner_cross_eq_zero_off_S_support
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S T : SmoothCcTensor g r s)
    {x : M} (hx : x ∉ tsupport S.toFun) :
    tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (T.toFun x) = 0 := by
  have hSx_zero : S.toFun x = 0 := by
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [hSx_zero]
  exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x (T.toFun x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_cross_eq_zero_off_S_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_cross_eq_zero_off_S_support target :: scope.openDecls } }


theorem continuous_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s) :
    Continuous (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) :=
  TensorRSBundle.continuous_inner_of_smooth_sections
    (I := I) (M := M) g r s
    (fun b : M => S.toSection b) (fun b : M => S.toSection b)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s S.toSection α)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s S.toSection α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_self ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_self


theorem continuous_inner_cross
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    Continuous (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (T.toFun b)) :=
  TensorRSBundle.continuous_inner_of_smooth_sections
    (I := I) (M := M) g r s
    (fun b : M => S.toSection b) (fun b : M => T.toSection b)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s S.toSection α)
    (fun α : M =>
      TensorMetricLowering.continuous_loweredCompose
        (I := I) (M := M) g r s T.toSection α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross


theorem aestronglyMeasurable_inner_self
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (S.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (continuous_inner_self (I := I) (M := M) S).aestronglyMeasurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_self ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_self


theorem aestronglyMeasurable_inner_cross
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (continuous_inner_cross (I := I) (M := M) S T).aestronglyMeasurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_cross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_cross ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.aestronglyMeasurable_inner_cross


theorem integrable_inner_cross
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (S.toFun x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (continuous_inner_cross (I := I) (M := M) S T).integrable_of_hasCompactSupport
    (hasCompactSupport_inner_cross (I := I) (M := M) S T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross


theorem memL2_toFun
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (S : SmoothCcTensor g r s) :
    MemL2 (I := I) (M := M) g r s S.toFun :=
  integrable_inner_cross (I := I) (M := M) S S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.memL2_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.memL2_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.memL2_toFun ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.memL2_toFun

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
