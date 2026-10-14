import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.L2
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
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

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

noncomputable def H1ComplBilin (g : SmoothRiemannianMetric I M) :
    H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ :=
  innerSL ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplBilin

@[simp] lemma H1ComplBilin_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Compl g) :
    H1ComplBilin (I := I) (M := M) g u v = ⟪u, v⟫_ℝ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_apply

lemma H1ComplBilin_isCoercive (g : SmoothRiemannianMetric I M) :
    IsCoercive (H1ComplBilin (I := I) (M := M) g) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show H1ComplBilin (I := I) (M := M) g u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_isCoercive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_isCoercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_isCoercive ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplBilin_isCoercive

noncomputable def lpFunctionalCLM (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      (H1Compl g →L[ℝ] ℝ) :=
  let applyL : (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
      (H1Compl g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →L[ℝ]
        (H1Compl g →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (H1Compl g)
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) ℝ
  ((applyL.flip) (H1ComplToLp (I := I) (M := M) g)).comp
    (innerSL ℝ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM ``Submission.DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM

@[simp] lemma lpFunctionalCLM_apply (g : SmoothRiemannianMetric I M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    lpFunctionalCLM (I := I) (M := M) g f v =
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  change (innerSL ℝ f) (H1ComplToLp (I := I) (M := M) g v) =
    ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (H1ComplToLp (I := I) (M := M) g v) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.lpFunctionalCLM_apply

noncomputable def H1ComplLaxMilgramEquiv (g : SmoothRiemannianMetric I M) :
    H1Compl g ≃L[ℝ] H1Compl g :=
  IsCoercive.continuousLinearEquivOfBilin
    (H1ComplBilin_isCoercive (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv

@[simp] lemma H1ComplLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric I M) (u w : H1Compl g) :
    ⟪H1ComplLaxMilgramEquiv (I := I) (M := M) g u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplLaxMilgramEquiv_apply

noncomputable def H1ComplRieszRepr (g : SmoothRiemannianMetric I M) :
    (H1Compl g →L[ℝ] ℝ) →L[ℝ] H1Compl g :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (H1Compl g)).symm φ
      map_add' := fun φ ψ => by
        exact (InnerProductSpace.toDual ℝ (H1Compl g)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (H1Compl g)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (H1Compl g)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (H1Compl g)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (H1Compl g)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq ((InnerProductSpace.toDual ℝ (H1Compl g)).symm.norm_map φ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr

lemma H1ComplRieszRepr_inner (g : SmoothRiemannianMetric I M)
    (φ : H1Compl g →L[ℝ] ℝ) (w : H1Compl g) :
    ⟪H1ComplRieszRepr (I := I) (M := M) g φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (H1Compl g)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H1Compl g) (x := w) (y := φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr_inner ``Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplRieszRepr_inner

noncomputable def resolvent (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] H1Compl g :=
  (H1ComplRieszRepr (I := I) (M := M) g).comp
    (lpFunctionalCLM (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolvent ``Submission.DifferentialGeometry.Analysis.Laplacian.resolvent

theorem resolvent_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric I M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    ⟪resolvent (I := I) (M := M) g f, v⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  unfold resolvent
  rw [ContinuousLinearMap.comp_apply, H1ComplRieszRepr_inner,
    lpFunctionalCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolvent_inner_eq_lpFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolvent_inner_eq_lpFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolvent_inner_eq_lpFunctional ``Submission.DifferentialGeometry.Analysis.Laplacian.resolvent_inner_eq_lpFunctional

theorem resolvent_bilin_eq_lpFunctional
    (g : SmoothRiemannianMetric I M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    H1ComplBilin (I := I) (M := M) g
        (resolvent (I := I) (M := M) g f) v =
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  rw [H1ComplBilin_apply]
  exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.resolvent_bilin_eq_lpFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.resolvent_bilin_eq_lpFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.resolvent_bilin_eq_lpFunctional ``Submission.DifferentialGeometry.Analysis.Laplacian.resolvent_bilin_eq_lpFunctional

end Laplacian
end Analysis
end DifferentialGeometry

end
