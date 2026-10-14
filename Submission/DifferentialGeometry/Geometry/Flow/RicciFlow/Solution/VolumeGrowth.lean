import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeVariation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (compact_ricciFlow_volumeVariation_on_regular)
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }

namespace SolutionOn

theorem hasDerivAt_volume (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt
      (fun s : ℝ => (riemannianVolumeMeasure I M (S.family.metric s) _root_.Set.univ).toReal)
      (-(∫ x, S.scalar t x ∂riemannianVolumeMeasure I M (S.family.metric t))) t := by
  have h := compact_ricciFlow_volumeVariation_on_regular S hS
    (fun _ _ => (1 : ℝ)) contMDiffOn_const ht
  simpa only [deriv_const, mul_one, zero_sub, _root_.MeasureTheory.integral_neg, _root_.MeasureTheory.integral_const,
    smul_eq_mul, Measure.real_def] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_volume

theorem hasDerivAt_exp_mul_volume (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (K : ℝ) {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt
      (fun s : ℝ => Real.exp (-K * s) *
        (riemannianVolumeMeasure I M (S.family.metric s) _root_.Set.univ).toReal)
      (∫ x, (Real.exp (-K * t) * (-K) - S.scalar t x * Real.exp (-K * t))
        ∂riemannianVolumeMeasure I M (S.family.metric t)) t := by
  have hweight : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (fun s : ℝ => Real.exp (-K * s)) := by
    rw [contMDiff_iff_contDiff]
    exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hweight' : HasDerivAt (fun s : ℝ => Real.exp (-K * s))
      (Real.exp (-K * t) * (-K)) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (-K)).exp
  have h := compact_ricciFlow_volumeVariation_on_regular S hS
    (fun s _ => Real.exp (-K * s)) (hweight.comp contMDiff_fst).contMDiffOn ht
  simp only [hweight'.deriv, _root_.MeasureTheory.integral_const, smul_eq_mul, Measure.real_def] at h
  convert h using 1
  funext s
  exact mul_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_exp_mul_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_exp_mul_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_exp_mul_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_exp_mul_volume

theorem antitoneOn_exp_mul_volume (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (K : ℝ) {J : Set ℝ} (hJ : Convex ℝ J)
    (hregular : J ⊆ D.regular) (hscalar : ∀ t ∈ J, ∀ x : M, -K ≤ S.scalar t x) :
    AntitoneOn
      (fun t : ℝ => Real.exp (-K * t) *
        (riemannianVolumeMeasure I M (S.family.metric t) _root_.Set.univ).toReal) J := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos hJ
  · intro t ht
    exact (S.hasDerivAt_exp_mul_volume hS K (hregular ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (S.hasDerivAt_exp_mul_volume hS K
      (hregular (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    apply _root_.MeasureTheory.integral_nonpos
    intro x
    have hbound := hscalar t (interior_subset ht) x
    have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-K * t)).le
    change Real.exp (-K * t) * (-K) - S.scalar t x * Real.exp (-K * t) ≤ 0
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.antitoneOn_exp_mul_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.antitoneOn_exp_mul_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.antitoneOn_exp_mul_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.antitoneOn_exp_mul_volume

end SolutionOn

end DifferentialGeometry.PDE.RicciFlow
