import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Spectral.IteratedDomain

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

theorem heatSemigroup_in_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow

noncomputable def heatSemigroupSpectralLift
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    H1Compl (I := I) (M := M) g :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift

theorem heatSemigroupSpectralLift_mem
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k ∈
      laplacianDomainPow (I := I) (M := M) g k :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_mem ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroupSpectralLift_mem

theorem H1ComplToLp_heatSemigroupSpectralLift
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    H1ComplToLp (I := I) (M := M) g
        (heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k) =
      heatSemigroup (I := I) (M := M) g t u_0 :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose_spec.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupSpectralLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupSpectralLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupSpectralLift ``Submission.DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupSpectralLift

noncomputable def heatSemigroupExplicitLift
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (iteratedResolventL2 (I := I) (M := M) g k
      (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift

theorem heatSemigroupExplicitLift_mem
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupExplicitLift (I := I) (M := M) g k t u_0 ∈
      laplacianDomainPow (I := I) (M := M) g (k + 1) := by
  unfold heatSemigroupExplicitLift
  rw [laplacianDomainPow_succ_mem_iff]
  exact ⟨oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_mem ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroupExplicitLift_mem

theorem H1ComplToLp_heatSemigroupExplicitLift
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    H1ComplToLp (I := I) (M := M) g
        (heatSemigroupExplicitLift (I := I) (M := M) g k t u_0) =
      heatSemigroup (I := I) (M := M) g t u_0 := by
  unfold heatSemigroupExplicitLift
  rw [show H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k
            (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0))) =
      resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k
          (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0)) from
    (resolventL2_apply (I := I) (M := M) g _).symm]
  rw [show resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k
          (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0)) =
      iteratedResolventL2 (I := I) (M := M) g (k + 1)
        (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0) from
    (iteratedResolventL2_succ_apply (I := I) (M := M) g k _).symm]
  exact iteratedResolventL2_oneMinusLapHeat_apply (I := I) (M := M) g (k + 1) ht u_0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupExplicitLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupExplicitLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupExplicitLift ``Submission.DifferentialGeometry.Analysis.HeatEquation.H1ComplToLp_heatSemigroupExplicitLift

theorem heatSemigroup_in_laplacianDomainPow_succ_explicit
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1) ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  ⟨heatSemigroupExplicitLift (I := I) (M := M) g k t u_0,
    heatSemigroupExplicitLift_mem (I := I) (M := M) g k t u_0,
    H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g k ht u_0⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow_succ_explicit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow_succ_explicit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow_succ_explicit ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_in_laplacianDomainPow_succ_explicit

end HeatEquation
end Analysis
end DifferentialGeometry

end
