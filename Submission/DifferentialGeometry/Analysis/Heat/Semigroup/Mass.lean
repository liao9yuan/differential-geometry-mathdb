import Submission.DifferentialGeometry.Analysis.Heat.Semigroup.Solution.Duhamel
import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Regularity.ClosedManifold
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.SmoothBridge
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

abbrev heatMassSpace (g : SmoothRiemannianMetric I M) :=
  _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure I M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatMassSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatMassSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatMassSpace ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatMassSpace

noncomputable def heatMassOne (g : SmoothRiemannianMetric I M) : heatMassSpace g := by
  classical
  letI : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact _root_.MeasureTheory.indicatorConstLp 2 (MeasurableSet.univ : MeasurableSet (Set.univ : Set M))
    (_root_.MeasureTheory.measure_ne_top (riemannianVolumeMeasure I M g) Set.univ) (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatMassOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatMassOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatMassOne ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatMassOne

noncomputable def heatMass (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) (t : ℝ) : ℝ :=
  ⟪heatMassOne (I := I) (M := M) g, heatSemigroup (I := I) (M := M) g t u₀⟫_ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatMass ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatMass

theorem heatMass_eq_integral
    (g : SmoothRiemannianMetric I M) (v : heatMassSpace g)
    (s : ℝ) :
    heatMass (I := I) (M := M) g v s =
      ∫ x, ((heatSemigroup (I := I) (M := M) g s v : heatMassSpace g) : M → ℝ) x
        ∂(riemannianVolumeMeasure I M g) := by
  classical
  set μ := riemannianVolumeMeasure I M g with hμ
  let : _root_.MeasureTheory.IsFiniteMeasure μ := by
    rw [hμ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  unfold heatMass
  calc
    ⟪heatMassOne (I := I) (M := M) g, heatSemigroup (I := I) (M := M) g s v⟫_ℝ =
        ∫ x in Set.univ, ((heatSemigroup (I := I) (M := M) g s v :
            heatMassSpace g) : M → ℝ) x ∂μ := by
      exact MeasureTheory.L2.inner_indicatorConstLp_one
        (μ := μ) (𝕜 := ℝ)
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set M))
        (_root_.MeasureTheory.measure_ne_top μ Set.univ) (heatSemigroup (I := I) (M := M) g s v)
    _ = ∫ x, ((heatSemigroup (I := I) (M := M) g s v : heatMassSpace g) : M → ℝ) x ∂μ :=
      _root_.MeasureTheory.setIntegral_univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatMass_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatMass_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatMass_eq_integral ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatMass_eq_integral

theorem heatMass_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s)
      ⟪heatMassOne (I := I) (M := M) g, -(heatPower (I := I) (M := M) g 1 t u₀)⟫_ℝ t := by
  obtain ⟨u_smooth, du_smooth, hu, hdu, hderiv, hlap⟩ :=
    heatSemigroup_has_smooth_generator_representative_of_closed (I := I) (M := M) g ht u₀
  let L : heatMassSpace g →L[ℝ] ℝ :=
    innerSL (𝕜 := ℝ) (E := heatMassSpace g)
      (heatMassOne (I := I) (M := M) g)
  have hcomp : HasDerivAt (fun s : ℝ =>
      L (heatSemigroup (I := I) (M := M) g s u₀))
      (L (smoothToLp (I := I) (M := M) g du_smooth)) t := by
    exact HasFDerivAt.comp_hasDerivAt t L.hasFDerivAt hderiv
  have hmass_eq : (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s) =
      fun s : ℝ => L (heatSemigroup (I := I) (M := M) g s u₀) := by
    funext s
    rfl
  have hval_eq : ⟪heatMassOne (I := I) (M := M) g, -(heatPower (I := I) (M := M) g 1 t u₀)⟫_ℝ =
      L (smoothToLp (I := I) (M := M) g du_smooth) := by
    rw [hdu]
    rfl
  simpa [hmass_eq, hval_eq] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatMass_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatMass_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatMass_hasDerivAt ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatMass_hasDerivAt

theorem heatMass_deriv_zero
    (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s) 0 t := by
  have hderiv := heatMass_hasDerivAt (I := I) (M := M) g u₀ ht
  have hval : ⟪heatMassOne (I := I) (M := M) g,
      -(heatPower (I := I) (M := M) g 1 t u₀)⟫_ℝ = 0 := by
    obtain ⟨u_smooth, du_smooth, hu, hdu, hderiv', hlap⟩ :=
      heatSemigroup_has_smooth_generator_representative_of_closed (I := I) (M := M) g ht u₀
    rw [← hdu]
    classical
    set μ := riemannianVolumeMeasure I M g with hμ
    let : _root_.MeasureTheory.IsFiniteMeasure μ := by
      rw [hμ]
      exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
    have hinner :
        ⟪heatMassOne (I := I) (M := M) g, smoothToLp (I := I) (M := M) g du_smooth⟫_ℝ =
          ∫ x in Set.univ, ((smoothToLp (I := I) (M := M) g du_smooth :
            heatMassSpace g) : M → ℝ) x ∂μ := by
      exact MeasureTheory.L2.inner_indicatorConstLp_one
        (μ := μ) (𝕜 := ℝ)
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set M))
        (_root_.MeasureTheory.measure_ne_top μ Set.univ) (smoothToLp (I := I) (M := M) g du_smooth)
    rw [hinner]
    rw [_root_.MeasureTheory.setIntegral_univ]
    have hae := MemLp.coeFn_toLp (f := du_smooth.toFun) (p := (2 : ℝ≥0∞))
      (μ := μ) du_smooth.memLp_two
    have hint_congr : (∫ x, ((smoothToLp (I := I) (M := M) g du_smooth :
        heatMassSpace g) : M → ℝ) x ∂μ) =
        ∫ x, du_smooth.toFun x ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact hae
    rw [hint_congr]
    have htoFun : du_smooth.toFun = ΔG (I := I) g u_smooth.toContMDiffMap := by
      rw [← congrArg SmoothScalar.toFun hlap]
      exact SmoothScalar.laplacian_toFun u_smooth
    rw [htoFun]
    exact laplacian_integral_eq_zero (I := I) (M := M) g u_smooth.smooth
  simpa [hval] using hderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatMass_deriv_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatMass_deriv_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatMass_deriv_zero ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatMass_deriv_zero

theorem heatSemigroup_mass_invariant
    (g : SmoothRiemannianMetric I M)
    (u₀ : heatMassSpace g) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, ((heatSemigroup (I := I) (M := M) g t u₀ : heatMassSpace g) : M → ℝ) x
        ∂(riemannianVolumeMeasure I M g)) =
      ∫ x, ((u₀ : heatMassSpace g) : M → ℝ) x
        ∂(riemannianVolumeMeasure I M g) := by
  classical
  set μ := riemannianVolumeMeasure I M g with hμ
  let : _root_.MeasureTheory.IsFiniteMeasure μ := by
    rw [hμ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let L : heatMassSpace g →L[ℝ] ℝ :=
    innerSL (𝕜 := ℝ) (E := heatMassSpace g)
      (heatMassOne (I := I) (M := M) g)
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst t
    simp [heatSemigroup_zero]
  · have hcont : ContinuousOn (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s)
        (_root_.Set.Icc 0 t) := by
      have hcontIci := heatSemigroup_continuous_on_nonneg (I := I) (M := M) g u₀
      have hcomp : ContinuousOn (fun s : ℝ =>
          L (heatSemigroup (I := I) (M := M) g s u₀)) (_root_.Set.Ici 0) :=
        L.continuous.comp_continuousOn hcontIci
      exact hcomp.mono (by intro p hp; exact hp.1)
    have hconst_on : ∀ ε ∈ _root_.Set.Ioo 0 t,
        heatMass (I := I) (M := M) g u₀ ε = heatMass (I := I) (M := M) g u₀ t := by
      intro ε hε
      have hderiv : ∀ x ∈ _root_.Set.Ico ε t,
          HasDerivWithinAt (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s) 0 (_root_.Set.Ici x) x := by
        intro x hx
        exact (heatMass_deriv_zero (I := I) (M := M) g u₀
          (lt_of_lt_of_le hε.1 hx.1)).hasDerivWithinAt
      have hconst_ε := constant_of_has_deriv_right_zero
        (f := fun s : ℝ => heatMass (I := I) (M := M) g u₀ s)
        (hcont.mono (Set.Icc_subset_Icc (le_of_lt hε.1) le_rfl)) hderiv t
        ⟨le_of_lt hε.2, le_rfl⟩
      exact hconst_ε.symm
    have h_ev : (fun ε : ℝ => heatMass (I := I) (M := M) g u₀ ε) =ᶠ[𝓝[>] (0 : ℝ)]
        fun _ : ℝ => heatMass (I := I) (M := M) g u₀ t := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{x : ℝ | 0 < x} ∩ Set.Iio t, ?_, ?_⟩
      · exact _root_.Filter.inter_mem self_mem_nhdsWithin
          (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htpos))
      intro ε hε
      exact hconst_on ε hε
    have h_tend : _root_.Filter.Tendsto (fun ε : ℝ => heatMass (I := I) (M := M) g u₀ ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (heatMass (I := I) (M := M) g u₀ t)) := by
      exact Filter.Tendsto.congr' h_ev.symm
        (tendsto_const_nhds (x := heatMass (I := I) (M := M) g u₀ t))
    have h_tend0 : _root_.Filter.Tendsto (fun ε : ℝ => heatMass (I := I) (M := M) g u₀ ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (heatMass (I := I) (M := M) g u₀ 0)) := by
      have hcontLp0 := heatSemigroup_continuous_at_zero (I := I) (M := M) g u₀
      have hL : _root_.Filter.Tendsto (fun s : ℝ =>
          L (heatSemigroup (I := I) (M := M) g s u₀)) (𝓝[≥] (0 : ℝ)) (𝓝 (L u₀)) :=
        (L.continuous.continuousAt (x := u₀)).tendsto.comp hcontLp0
      have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] (0 : ℝ) := by
        exact nhdsWithin_mono (x := (0 : ℝ))
          (s := {x : ℝ | 0 < x}) (t := {x : ℝ | 0 ≤ x})
          (by intro x hx; dsimp at hx ⊢; exact le_of_lt hx)
      have hL' : _root_.Filter.Tendsto (fun s : ℝ =>
          L (heatSemigroup (I := I) (M := M) g s u₀)) (𝓝[>] (0 : ℝ)) (𝓝 (L u₀)) :=
        hL.mono_left hmono
      change _root_.Filter.Tendsto (fun s : ℝ => heatMass (I := I) (M := M) g u₀ s) _ _ at hL'
      convert hL' using 1
      rw [heatMass, heatSemigroup_zero]
      rw [ContinuousLinearMap.id_apply]
      simp only [L, innerSL_apply_apply]
    have hconst := tendsto_nhds_unique h_tend h_tend0
    calc
      (∫ x, ((heatSemigroup (I := I) (M := M) g t u₀ : heatMassSpace g) : M → ℝ) x
          ∂(riemannianVolumeMeasure I M g)) =
          heatMass (I := I) (M := M) g u₀ t :=
        (heatMass_eq_integral (I := I) (M := M) g u₀ t).symm
      _ = heatMass (I := I) (M := M) g u₀ 0 := hconst
      _ = ∫ x, ((u₀ : heatMassSpace g) : M → ℝ) x
          ∂(riemannianVolumeMeasure I M g) := by
        rw [heatMass_eq_integral (I := I) (M := M) g u₀ 0]
        simp [heatSemigroup_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_mass_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_mass_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_mass_invariant ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_mass_invariant

end HeatEquation
end Analysis
end DifferentialGeometry

end
