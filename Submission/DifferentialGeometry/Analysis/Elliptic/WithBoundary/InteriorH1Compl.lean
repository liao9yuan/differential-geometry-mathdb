import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorSmoothScalarPreH1
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.I_half target :: scope.openDecls } }

variable [T2Space M] [CompactSpace M]

abbrev H1ComplInterior (g : SmoothRiemannianMetric (I_half n) M) : Type _ :=
  UniformSpace.Completion (InteriorSmoothScalar g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInterior ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInterior

noncomputable def smoothToH1ComplInterior (g : SmoothRiemannianMetric (I_half n) M) :
    InteriorSmoothScalar g →L[ℝ] H1ComplInterior g :=
  UniformSpace.Completion.toComplL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior

@[simp] lemma smoothToH1ComplInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    smoothToH1ComplInterior g f = (f : H1ComplInterior g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToH1ComplInterior_apply

lemma InteriorSmoothScalar.memLp_two
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    MemLp f.toFun 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact f.smooth.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.memLp_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.memLp_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.memLp_two ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.memLp_two

noncomputable def smoothToLpLinInterior (g : SmoothRiemannianMetric (I_half n) M) :
    InteriorSmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) where
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
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior

@[simp] lemma smoothToLpLinInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    smoothToLpLinInterior g f = f.memLp_two.toLp f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpLinInterior_apply

lemma InteriorSmoothScalar.norm_smoothToLp_sq
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (smoothToLpLinInterior g f)
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)] at h
  have hae : (fun a : M =>
        @_root_.Inner.inner ℝ _ _
          ((smoothToLpLinInterior g f : _root_.MeasureTheory.Lp ℝ 2 _) a)
          ((smoothToLpLinInterior g f : _root_.MeasureTheory.Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
      (fun a : M => f.toFun a * f.toFun a) := by
    have hae_coe : (smoothToLpLinInterior g f : _root_.MeasureTheory.Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g] f.toFun :=
      MemLp.coeFn_toLp f.memLp_two
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rfl
  rw [_root_.MeasureTheory.integral_congr_ae hae] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq

lemma InteriorSmoothScalar.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖f‖ ^ 2 = interiorSmoothScalarH1Inner f f := by
  have h := real_inner_self_eq_norm_sq f
  rw [InteriorSmoothScalar.inner_def] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_sq_eq_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_sq_eq_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_sq_eq_inner_self ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_sq_eq_inner_self

lemma InteriorSmoothScalar.norm_smoothToLp_sq_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [f.norm_smoothToLp_sq, f.norm_sq_eq_inner_self]
  unfold interiorSmoothScalarH1Inner
  have h_grad_nonneg :
      0 ≤ ∫ x, g.inner x ((gradGWithBoundarySection
              (I := I_half n) g f.smooth f.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((gradGWithBoundarySection
              (I := I_half n) g f.smooth f.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    f.integral_inner_grad_self_nonneg
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_sq_le

lemma InteriorSmoothScalar.norm_smoothToLp_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ≤ ‖f‖ := by
  have h_sq := f.norm_smoothToLp_sq_le
  have h_lhs_nn : 0 ≤ ‖smoothToLpLinInterior g f‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖f‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le

lemma InteriorSmoothScalar.norm_smoothToLp_le_one_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    ‖smoothToLpLinInterior g f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]; exact f.norm_smoothToLp_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le_one_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le_one_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le_one_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.norm_smoothToLp_le_one_mul

noncomputable def smoothToLpInterior (g : SmoothRiemannianMetric (I_half n) M) :
    InteriorSmoothScalar g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (smoothToLpLinInterior g).mkContinuous 1
    (fun f => f.norm_smoothToLp_le_one_mul)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior

@[simp] lemma smoothToLpInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    smoothToLpInterior g f = f.memLp_two.toLp f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.smoothToLpInterior_apply

private lemma denseRange_toComplL_interiorSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g →L[ℝ] H1ComplInterior g) := by
  rw [show (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g → H1ComplInterior g) =
      ((↑) : InteriorSmoothScalar g →
        UniformSpace.Completion (InteriorSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.denseRange_toComplL_interiorSmoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.denseRange_toComplL_interiorSmoothScalar target :: scope.openDecls } }

private lemma isUniformInducing_toComplL_interiorSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        InteriorSmoothScalar g →L[ℝ] H1ComplInterior g) := by
  rw [show (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g → H1ComplInterior g) =
      ((↑) : InteriorSmoothScalar g →
        UniformSpace.Completion (InteriorSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (InteriorSmoothScalar g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.isUniformInducing_toComplL_interiorSmoothScalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.isUniformInducing_toComplL_interiorSmoothScalar target :: scope.openDecls } }

noncomputable def H1ComplInteriorToLp
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplInterior g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ContinuousLinearMap.extend (smoothToLpInterior g)
    (UniformSpace.Completion.toComplL :
      InteriorSmoothScalar g →L[ℝ] H1ComplInterior g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp

lemma H1ComplInteriorToLp_smoothToH1ComplInterior
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : InteriorSmoothScalar g) :
    H1ComplInteriorToLp g (smoothToH1ComplInterior g f) =
      smoothToLpInterior g f := by
  unfold H1ComplInteriorToLp
  exact ContinuousLinearMap.extend_eq (smoothToLpInterior g)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_interiorSmoothScalar g)
    (isUniformInducing_toComplL_interiorSmoothScalar g) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp_smoothToH1ComplInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp_smoothToH1ComplInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp_smoothToH1ComplInterior ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorToLp_smoothToH1ComplInterior

end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
