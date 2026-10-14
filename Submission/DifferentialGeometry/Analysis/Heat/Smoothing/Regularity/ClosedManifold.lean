import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Regularity.ChartSobolev
import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Spectral.IteratedDomain
import Submission.DifferentialGeometry.Analysis.Heat.Semigroup.Generator
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.ChartH2kRegularity

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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge

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

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem chartSideH2kBridge_heat
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (k : ℕ) :
    ChartSideH2kBridge (I := I) (M := M) k
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all
      (I := I) (M := M) g ht u_0 k
  have h_bridge_lift :=
    chartSideH2kBridge_of_laplacianDomainPow
      (I := I) (M := M) g k hu_h_mem
  have h_coe : ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe] at h_bridge_lift
  exact h_bridge_lift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat ``Submission.DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat

theorem heatSemigroup_smooth_representative_of_closed
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth := by
  apply heatSemigroup_smooth_representative_of_chartSideBridges
    (I := I) (M := M) g u_0
  intro k
  exact chartSideH2kBridge_heat
    (I := I) (M := M) g ht u_0 k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_closed ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_closed

theorem heatPower_smooth_representative_of_closed
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_smooth : SmoothScalar g,
      ((heatPower (I := I) (M := M) g k t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth.toFun := by
  have hhalf : 0 < t / 2 := half_pos ht
  obtain ⟨u_smooth, hu_smooth, hu_ae⟩ :=
    heatSemigroup_smooth_representative_of_closed
      (I := I) (M := M) g hhalf
      (heatPower (I := I) (M := M) g k (t / 2) u_0)
  refine ⟨⟨u_smooth, hu_smooth⟩, ?_⟩
  have hfactor :
      heatSemigroup (I := I) (M := M) g (t / 2)
          (heatPower (I := I) (M := M) g k (t / 2) u_0) =
        heatPower (I := I) (M := M) g k t u_0 := by
    have hcomp := heatSemigroup_comp_heatPower
      (I := I) (M := M) g k (t := t / 2) hhalf (s := t / 2) hhalf.le
    have happ := congrArg (fun A :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) => A u_0) hcomp
    simpa [ContinuousLinearMap.comp_apply] using happ
  rw [← hfactor]
  exact hu_ae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatPower_smooth_representative_of_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatPower_smooth_representative_of_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatPower_smooth_representative_of_closed ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatPower_smooth_representative_of_closed

theorem heatSemigroup_has_smooth_generator_representative_of_closed
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_smooth du_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g u_smooth =
        heatSemigroup (I := I) (M := M) g t u_0 ∧
      smoothToLp (I := I) (M := M) g du_smooth =
        -(heatPower (I := I) (M := M) g 1 t u_0) ∧
      HasDerivAt (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
        (smoothToLp (I := I) (M := M) g du_smooth) t ∧
      u_smooth.laplacian = du_smooth := by
  obtain ⟨u_fun, hu_smooth, hu_ae⟩ :=
    heatSemigroup_smooth_representative_of_closed
      (I := I) (M := M) g ht u_0
  let u_smooth : SmoothScalar g := ⟨u_fun, hu_smooth⟩
  have hu_lp : smoothToLp (I := I) (M := M) g u_smooth =
      heatSemigroup (I := I) (M := M) g t u_0 := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp u_smooth.memLp_two).trans hu_ae.symm
  obtain ⟨w_smooth, hw_ae⟩ :=
    heatPower_smooth_representative_of_closed
      (I := I) (M := M) g 1 ht u_0
  have hw_lp : smoothToLp (I := I) (M := M) g w_smooth =
      heatPower (I := I) (M := M) g 1 t u_0 := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp w_smooth.memLp_two).trans hw_ae.symm
  let du_smooth : SmoothScalar g := -w_smooth
  have hdu_lp : smoothToLp (I := I) (M := M) g du_smooth =
      -(heatPower (I := I) (M := M) g 1 t u_0) := by
    rw [show du_smooth = -w_smooth from rfl,
      map_neg, hw_lp]
  let u_dom : laplacianDomain (I := I) (M := M) g :=
    ⟨smoothToH1Compl (I := I) (M := M) g u_smooth,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u_smooth⟩
  let heat_dom : laplacianDomain (I := I) (M := M) g :=
    ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
      heatSemigroupExplicitLift_zero_mem_laplacianDomain
        (I := I) (M := M) g t u_0⟩
  have hu_dom_lp : H1ComplToLp (I := I) (M := M) g (u_dom : H1Compl g) =
      heatSemigroup (I := I) (M := M) g t u_0 := by
    change H1ComplToLp (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g u_smooth) = _
    rw [H1ComplToLp_smoothToH1Compl, hu_lp]
  have hheat_dom_lp : H1ComplToLp (I := I) (M := M) g (heat_dom : H1Compl g) =
      heatSemigroup (I := I) (M := M) g t u_0 := by
    exact H1ComplToLp_heatSemigroupExplicitLift
      (I := I) (M := M) g 0 ht u_0
  have hdom : u_dom = heat_dom := by
    apply Subtype.ext
    exact H1ComplToLp_injective_on_laplacianDomain
      (I := I) (M := M) g (hu_dom_lp.trans hheat_dom_lp.symm)
  have hu_laplacian :
      laplacianOp (I := I) (M := M) g u_dom =
        -(heatPower (I := I) (M := M) g 1 t u_0) := by
    rw [hdom]
    exact laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
      (I := I) (M := M) g ht u_0
  have hlaplacian_lp :
      smoothToLp (I := I) (M := M) g u_smooth.laplacian =
        smoothToLp (I := I) (M := M) g du_smooth := by
    rw [hdu_lp, ← hu_laplacian]
    exact (laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian
      (I := I) (M := M) u_smooth).symm
  have hlaplacian : u_smooth.laplacian = du_smooth :=
    smoothToLp_injective (I := I) (M := M) g hlaplacian_lp
  have hderiv := hasDerivAt_heatSemigroup_eq_laplacianOp
    (I := I) (M := M) g ht u_0
  rw [laplacianOp_heatSemigroupExplicitLift_zero_eq_neg_heatPower_one
    (I := I) (M := M) g ht u_0, ← hdu_lp] at hderiv
  exact ⟨u_smooth, du_smooth, hu_lp, hdu_lp, hderiv, hlaplacian⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_has_smooth_generator_representative_of_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_has_smooth_generator_representative_of_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_has_smooth_generator_representative_of_closed ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_has_smooth_generator_representative_of_closed

theorem heatSemigroup_smooth_in_space_and_time
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∀ t : ℝ, 0 < t →
      ∃ u_smooth_t : M → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth_t ∧
        ((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I) (M := M) g] u_smooth_t) ∧
    ContDiffOn ℝ ∞
      (fun t : ℝ =>
        (heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)))
      (Set.Ioi (0 : ℝ)) := by
  apply heatSemigroup_smooth_in_space_and_time_of_chartSideBridges
    (I := I) (M := M) g u_0
  intro t ht k
  exact chartSideH2kBridge_heat
    (I := I) (M := M) g ht u_0 k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time

end HeatEquation
end Analysis
end DifferentialGeometry

end
