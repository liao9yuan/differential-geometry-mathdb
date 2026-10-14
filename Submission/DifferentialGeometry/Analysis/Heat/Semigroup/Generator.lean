import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Spectral.Lift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

lemma oneMinusLapHeat_one_apply
    (g : SmoothRiemannianMetric I M) (t : ℝ)
    (u : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    oneMinusLapHeat (I := I) (M := M) g 1 t u =
      heatSemigroup (I := I) (M := M) g t u +
        heatPower (I := I) (M := M) g 1 t u := by
  rw [oneMinusLapHeat_apply]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, one_smul]
  rw [heatPower_zero (I := I) (M := M) g t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.oneMinusLapHeat_one_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.oneMinusLapHeat_one_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.oneMinusLapHeat_one_apply ``Submission.DifferentialGeometry.Analysis.HeatEquation.oneMinusLapHeat_one_apply

lemma heatSemigroupExplicitLift_zero_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (t : ℝ)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 ∈
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomain_mem_iff]
  refine ⟨oneMinusLapHeat (I := I) (M := M) g 1 t u_0, ?_⟩
  unfold heatSemigroupExplicitLift
  rw [iteratedResolventL2_zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_zero_mem_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_zero_mem_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_zero_mem_laplacianDomain ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_zero_mem_laplacianDomain

theorem laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    laplacianOp (I := I) (M := M) g
        ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
          heatSemigroupExplicitLift_zero_mem_laplacianDomain
            (I := I) (M := M) g t u_0⟩ =
      -(heatPower (I := I) (M := M) g 1 t u_0) := by
  set f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    oneMinusLapHeat (I := I) (M := M) g 1 t u_0 with hf_def
  have h_lift_eq :
      heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 =
        resolvent (I := I) (M := M) g f := by
    unfold heatSemigroupExplicitLift
    rw [iteratedResolventL2_zero_apply]
  rw [show (⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
        heatSemigroupExplicitLift_zero_mem_laplacianDomain
          (I := I) (M := M) g t u_0⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨resolvent (I := I) (M := M) g f,
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ from ?_]
  · rw [laplacianOp_resolvent (I := I) (M := M) g f]
    have h_H1 : H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g f) =
        heatSemigroup (I := I) (M := M) g t u_0 := by
      have := H1ComplToLp_heatSemigroupExplicitLift
        (I := I) (M := M) g 0 ht u_0
      rwa [h_lift_eq] at this
    rw [h_H1]
    rw [hf_def, oneMinusLapHeat_one_apply (I := I) (M := M) g t u_0]
    abel
  · apply Subtype.ext
    exact h_lift_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one ``Submission.DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one

theorem hasDerivAt_heatSemigroup_eq_laplacianOp
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    HasDerivAt (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (laplacianOp (I := I) (M := M) g
        ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
          heatSemigroupExplicitLift_zero_mem_laplacianDomain
            (I := I) (M := M) g t u_0⟩)
      t := by
  have h_op := hasDerivAt_heatSemigroup (I := I) (M := M) g ht
  have h_u_const : HasDerivAt (fun _ : ℝ => u_0) (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) t :=
    hasDerivAt_const t u_0
  have h_apply : HasDerivAt
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      ((-heatPower (I := I) (M := M) g 1 t) u_0 +
        heatSemigroup (I := I) (M := M) g t 0) t :=
    h_op.clm_apply h_u_const
  have h_simp :
      ((-heatPower (I := I) (M := M) g 1 t) u_0 +
        heatSemigroup (I := I) (M := M) g t 0) =
      -(heatPower (I := I) (M := M) g 1 t u_0) := by
    rw [(heatSemigroup (I := I) (M := M) g t).map_zero]
    rw [add_zero]
    rfl
  rw [h_simp] at h_apply
  rw [laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
    (I := I) (M := M) g ht u_0]
  exact h_apply

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.hasDerivAt_heatSemigroup_eq_laplacianOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.hasDerivAt_heatSemigroup_eq_laplacianOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.hasDerivAt_heatSemigroup_eq_laplacianOp ``Submission.DifferentialGeometry.Analysis.HeatEquation.hasDerivAt_heatSemigroup_eq_laplacianOp

lemma heatSemigroupSpectralLift_one_eq_explicit_zero
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 :
        H1Compl (I := I) (M := M) g) =
      heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 := by
  have h_can_mem_pow : heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 ∈
      laplacianDomainPow (I := I) (M := M) g 1 :=
    heatSemigroupSpectralLift_mem (I := I) (M := M) g ht u_0 1
  have h_can_mem : heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 ∈
      laplacianDomain (I := I) (M := M) g := by
    rw [← laplacianDomainPow_one (I := I) (M := M) g]
    exact h_can_mem_pow
  have h_exp_mem : heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0 ∈
      laplacianDomain (I := I) (M := M) g :=
    heatSemigroupExplicitLift_zero_mem_laplacianDomain
      (I := I) (M := M) g t u_0
  have h_proj_eq :
      H1ComplToLp (I := I) (M := M) g
        (heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1) =
      H1ComplToLp (I := I) (M := M) g
        (heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0) := by
    rw [H1ComplToLp_heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1]
    rw [H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g 0 ht u_0]
  exact H1ComplToLp_injective_on_laplacianDomain (I := I) (M := M) g
    (u := ⟨_, h_can_mem⟩) (v := ⟨_, h_exp_mem⟩) h_proj_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_one_eq_explicit_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_one_eq_explicit_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_one_eq_explicit_zero ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_one_eq_explicit_zero

theorem laplacianOp_heatSemigroupSpectralLift_one_eq_neg_heatPower_one
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    laplacianOp (I := I) (M := M) g
        ⟨(heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 :
            H1Compl (I := I) (M := M) g),
          by
            rw [← laplacianDomainPow_one (I := I) (M := M) g]
            exact heatSemigroupSpectralLift_mem
              (I := I) (M := M) g ht u_0 1⟩ =
      -(heatPower (I := I) (M := M) g 1 t u_0) := by
  rw [show (⟨(heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 1 :
        H1Compl (I := I) (M := M) g),
        by
          rw [← laplacianDomainPow_one (I := I) (M := M) g]
          exact heatSemigroupSpectralLift_mem
            (I := I) (M := M) g ht u_0 1⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
        heatSemigroupExplicitLift_zero_mem_laplacianDomain
          (I := I) (M := M) g t u_0⟩ from ?_]
  · exact laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
      (I := I) (M := M) g ht u_0
  · apply Subtype.ext
    exact heatSemigroupSpectralLift_one_eq_explicit_zero
      (I := I) (M := M) g ht u_0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupSpectralLift_one_eq_neg_heatPower_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupSpectralLift_one_eq_neg_heatPower_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupSpectralLift_one_eq_neg_heatPower_one ``Submission.DifferentialGeometry.Analysis.HeatEquation.laplacianOp_heatSemigroupSpectralLift_one_eq_neg_heatPower_one

end HeatEquation
end Analysis
end DifferentialGeometry

end
