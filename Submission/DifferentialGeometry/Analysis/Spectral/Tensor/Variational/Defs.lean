import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual

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
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def tensorH1ComplBilin (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorH1Compl g r s →L[ℝ] ℝ :=
  innerSL ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin


omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorH1ComplBilin_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u v : TensorH1Compl g r s) :
    tensorH1ComplBilin (I := I) (M := M) g r s u v = ⟪u, v⟫_ℝ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_apply


omit [NeZero (Module.finrank ℝ E)] in
lemma tensorH1ComplBilin_isCoercive (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCoercive (tensorH1ComplBilin (I := I) (M := M) g r s) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show tensorH1ComplBilin (I := I) (M := M) g r s u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_isCoercive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_isCoercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_isCoercive ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplBilin_isCoercive

noncomputable def tensorLpFunctionalCLM (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] (TensorH1Compl g r s →L[ℝ] ℝ) :=
  let applyL :
      (TensorL2 r s g →L[ℝ] ℝ) →L[ℝ]
        (TensorH1Compl g r s →L[ℝ] TensorL2 r s g) →L[ℝ]
        (TensorH1Compl g r s →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (TensorH1Compl g r s) (TensorL2 r s g) ℝ
  ((applyL.flip) (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)).comp
    (innerSL ℝ : TensorL2 r s g →L[ℝ] TensorL2 r s g →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM


omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorLpFunctionalCLM_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    tensorLpFunctionalCLM (I := I) (M := M) g r s f v =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  change (innerSL ℝ f) (TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) =
    ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorLpFunctionalCLM_apply

noncomputable def tensorH1ComplLaxMilgramEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s ≃L[ℝ] TensorH1Compl g r s :=
  IsCoercive.continuousLinearEquivOfBilin
    (tensorH1ComplBilin_isCoercive (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv


omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorH1ComplLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u w : TensorH1Compl g r s) :
    ⟪tensorH1ComplLaxMilgramEquiv (I := I) (M := M) g r s u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplLaxMilgramEquiv_apply

noncomputable def tensorH1ComplRieszRepr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (TensorH1Compl g r s →L[ℝ] ℝ) →L[ℝ] TensorH1Compl g r s :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ
      map_add' := fun φ ψ => by
        exact (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq
        ((InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm.norm_map φ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr


omit [NeZero (Module.finrank ℝ E)] in
lemma tensorH1ComplRieszRepr_inner (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : TensorH1Compl g r s →L[ℝ] ℝ) (w : TensorH1Compl g r s) :
    ⟪tensorH1ComplRieszRepr (I := I) (M := M) g r s φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply
    (𝕜 := ℝ) (E := TensorH1Compl g r s) (x := w) (y := φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr_inner ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1ComplRieszRepr_inner

noncomputable def tensorResolvent (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorH1Compl g r s :=
  (tensorH1ComplRieszRepr (I := I) (M := M) g r s).comp
    (tensorLpFunctionalCLM (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolvent_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    ⟪tensorResolvent (I := I) (M := M) g r s f, v⟫_ℝ =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  unfold tensorResolvent
  rw [ContinuousLinearMap.comp_apply, tensorH1ComplRieszRepr_inner,
    tensorLpFunctionalCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_inner_eq_lpFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_inner_eq_lpFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_inner_eq_lpFunctional ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_inner_eq_lpFunctional


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolvent_bilin_eq_lpFunctional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    tensorH1ComplBilin (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s f) v =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  rw [tensorH1ComplBilin_apply]
  exact tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s f v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_bilin_eq_lpFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_bilin_eq_lpFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_bilin_eq_lpFunctional ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolvent_bilin_eq_lpFunctional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
