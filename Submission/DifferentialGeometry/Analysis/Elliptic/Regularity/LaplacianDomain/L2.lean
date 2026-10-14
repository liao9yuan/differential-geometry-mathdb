import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.H1Compl.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [I.Boundaryless] in
lemma SmoothScalar.memLp_two {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    MemLp f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact f.smooth.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.memLp_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.memLp_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.memLp_two ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.memLp_two

noncomputable def smoothToLpLin (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →ₗ[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun f := f.memLp_two.toLp f.toFun
  map_add' f h := by
    have h_lhs_rfl : (f + h).memLp_two.toLp (f + h).toFun =
        (f.memLp_two.add h.memLp_two).toLp (f.toFun + h.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_add]
  map_smul' c f := by
    have h_lhs_rfl : (c • f).memLp_two.toLp (c • f).toFun =
        (f.memLp_two.const_smul c).toLp (c • f.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_const_smul]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToLpLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToLpLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToLpLin ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToLpLin

omit [I.Boundaryless] in
@[simp] lemma smoothToLpLin_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToLpLin (I := I) (M := M) g f = f.memLp_two.toLp f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToLpLin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToLpLin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToLpLin_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToLpLin_apply

omit [I.Boundaryless] in
lemma SmoothScalar.norm_smoothToLp_sq {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (smoothToLpLin (I := I) (M := M) g f)
  rw [L2.inner_def (𝕜 := ℝ)] at h
  have hae : (fun a : M =>
        @_root_.Inner.inner ℝ _ _
          ((smoothToLpLin (I := I) (M := M) g f : _root_.MeasureTheory.Lp ℝ 2 _) a)
          ((smoothToLpLin (I := I) (M := M) g f : _root_.MeasureTheory.Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun a : M => f.toFun a * f.toFun a) := by
    have hae_coe : (smoothToLpLin (I := I) (M := M) g f : _root_.MeasureTheory.Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] f.toFun :=
      MemLp.coeFn_toLp f.memLp_two
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rfl
  rw [_root_.MeasureTheory.integral_congr_ae hae] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq

lemma SmoothScalar.norm_sq_eq_inner_self {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖f‖ ^ 2 = smoothScalarH1Inner (I := I) (M := M) f f := by
  have h := real_inner_self_eq_norm_sq f
  rw [SmoothScalar.inner_def] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_sq_eq_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_sq_eq_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_sq_eq_inner_self ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_sq_eq_inner_self

lemma SmoothScalar.norm_smoothToLp_sq_le {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [f.norm_smoothToLp_sq, f.norm_sq_eq_inner_self]
  unfold smoothScalarH1Inner
  have h_grad_nonneg :
      0 ≤ ∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    f.integral_inner_grad_self_nonneg
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq_le ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_sq_le

lemma SmoothScalar.norm_smoothToLp_le {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ≤ ‖f‖ := by
  have h_sq := f.norm_smoothToLp_sq_le
  have h_lhs_nn : 0 ≤ ‖smoothToLpLin (I := I) (M := M) g f‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖f‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le

lemma SmoothScalar.norm_smoothToLp_le_one_mul {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]; exact f.norm_smoothToLp_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le_one_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le_one_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le_one_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.norm_smoothToLp_le_one_mul

noncomputable def smoothToLp (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothToLpLin (I := I) (M := M) g).mkContinuous 1
    (fun f => f.norm_smoothToLp_le_one_mul)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToLp

@[simp] lemma smoothToLp_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToLp (I := I) (M := M) g f =
      f.memLp_two.toLp f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToLp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToLp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToLp_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToLp_apply

theorem smoothToLp_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (smoothToLp (I := I) (M := M) g) := by
  intro f h hfh
  apply SmoothScalar.ext
  funext x
  have hf_ae : (smoothToLp (I := I) (M := M) g f : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] f.toFun :=
    MemLp.coeFn_toLp f.memLp_two
  have hh_ae : (smoothToLp (I := I) (M := M) g h : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] h.toFun :=
    MemLp.coeFn_toLp h.memLp_two
  have hlp_ae : (smoothToLp (I := I) (M := M) g f : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (smoothToLp (I := I) (M := M) g h : M → ℝ) := by
    rw [hfh]
  have hfun_ae : f.toFun =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] h.toFun :=
    hf_ae.symm.trans (hlp_ae.trans hh_ae)
  let : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact congrFun ((Continuous.ae_eq_iff_eq
    (riemannianVolumeMeasure (I := I) (M := M) g)
    f.smooth.continuous h.smooth.continuous).mp hfun_ae) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothToLp_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothToLp_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothToLp_injective ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothToLp_injective

private lemma denseRange_toComplL_smoothScalar (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.denseRange_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.denseRange_toComplL_smoothScalar target :: scope.openDecls } }

private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.isUniformInducing_toComplL_smoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.isUniformInducing_toComplL_smoothScalar target :: scope.openDecls } }

noncomputable def H1ComplToLp (g : SmoothRiemannianMetric I M) :
    H1Compl g →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ContinuousLinearMap.extend (smoothToLp (I := I) (M := M) g)
    (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplToLp

lemma H1ComplToLp_smoothToH1Compl (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g f) =
      smoothToLp (I := I) (M := M) g f := by
  unfold H1ComplToLp
  exact ContinuousLinearMap.extend_eq (smoothToLp (I := I) (M := M) g)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplToLp_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplToLp_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplToLp_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplToLp_smoothToH1Compl

end Laplacian
end Analysis
end DifferentialGeometry

end
