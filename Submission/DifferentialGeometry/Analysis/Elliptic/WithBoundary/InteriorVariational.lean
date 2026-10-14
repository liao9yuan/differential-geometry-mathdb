import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorH1Compl
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
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

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

noncomputable def H1ComplInteriorBilin
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplInterior g →L[ℝ] H1ComplInterior g →L[ℝ] ℝ :=
  innerSL ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin

@[simp] lemma H1ComplInteriorBilin_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : H1ComplInterior g) :
    H1ComplInteriorBilin g u v = ⟪u, v⟫_ℝ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_apply

lemma H1ComplInteriorBilin_isCoercive
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsCoercive (H1ComplInteriorBilin g) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show H1ComplInteriorBilin g u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_isCoercive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_isCoercive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_isCoercive ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorBilin_isCoercive

noncomputable def lpFunctionalCLMInterior
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      (H1ComplInterior g →L[ℝ] ℝ) :=
  letI : NormedAddCommGroup (H1ComplInterior g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let applyL : (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
      (H1ComplInterior g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) →L[ℝ]
        (H1ComplInterior g →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (H1ComplInterior g)
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) ℝ
  ((ContinuousLinearMap.flip (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
      (E := _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ)
      (F := H1ComplInterior g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
      (G := H1ComplInterior g →L[ℝ] ℝ) applyL) (H1ComplInteriorToLp g) :
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
        (H1ComplInterior g →L[ℝ] ℝ)).comp
    (innerSL ℝ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior

@[simp] lemma lpFunctionalCLMInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplInterior g) :
    lpFunctionalCLMInterior g f v =
      ⟪H1ComplInteriorToLp g v, f⟫_ℝ := by
  change (innerSL ℝ f) (H1ComplInteriorToLp g v) =
    ⟪H1ComplInteriorToLp g v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (H1ComplInteriorToLp g v) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.lpFunctionalCLMInterior_apply

noncomputable def H1ComplInteriorLaxMilgramEquiv
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplInterior g ≃L[ℝ] H1ComplInterior g :=
  IsCoercive.continuousLinearEquivOfBilin
    (H1ComplInteriorBilin_isCoercive g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv

@[simp] lemma H1ComplInteriorLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric (I_half n) M) (u w : H1ComplInterior g) :
    ⟪H1ComplInteriorLaxMilgramEquiv g u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorLaxMilgramEquiv_apply

noncomputable def H1ComplInteriorRieszRepr
    (g : SmoothRiemannianMetric (I_half n) M) :
    (H1ComplInterior g →L[ℝ] ℝ) →L[ℝ] H1ComplInterior g :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ
      map_add' := fun φ ψ =>
        (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq
        ((InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm.norm_map φ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr

lemma H1ComplInteriorRieszRepr_inner
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : H1ComplInterior g →L[ℝ] ℝ) (w : H1ComplInterior g) :
    ⟪H1ComplInteriorRieszRepr g φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H1ComplInterior g)
    (x := w) (y := φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr_inner ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.H1ComplInteriorRieszRepr_inner

noncomputable def resolventInterior
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplInterior g :=
  (H1ComplInteriorRieszRepr g).comp (lpFunctionalCLMInterior g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior

theorem resolventInterior_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplInterior g) :
    ⟪resolventInterior g f, v⟫_ℝ =
      ⟪H1ComplInteriorToLp g v, f⟫_ℝ := by
  unfold resolventInterior
  rw [ContinuousLinearMap.comp_apply, H1ComplInteriorRieszRepr_inner,
    lpFunctionalCLMInterior_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior_inner_eq_lpFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior_inner_eq_lpFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior_inner_eq_lpFunctional ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.resolventInterior_inner_eq_lpFunctional

end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
