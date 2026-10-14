import Submission.DifferentialGeometry.Analysis.Parabolic.Energy.DirichletQuotient
import Submission.DifferentialGeometry.Analysis.Parabolic.Energy.Continuity
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Energy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.HeatEnergy
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}
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

theorem heat_potential_eq_zero_of_terminal_eq_zero_on_surface
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2) {V u : ℝ → M → ℝ}
    (hu : IsHeatPotOn D (flowG S) V u)
    {a b : ℝ} (hab : a < b) (hcar : _root_.Set.Icc a b ⊆ D.carrier)
    (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (hV : ContinuousOn (fun p : ℝ × M => V p.1 p.2) (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hVsmooth : ∀ t ∈ _root_.Set.Ioo a b, ContMDiff I 𝓘(ℝ, ℝ) ∞ (V t))
    (hterminal : ∀ x, u b x = 0) : ∀ t ∈ _root_.Set.Icc a b, ∀ x, u t x = 0 := by
  let μ := fun t => riemannianVolumeMeasure I M (S.family.metric t)
  let energy := fun t => ∫ x, (u t x) ^ 2 ∂μ t
  let dirichlet := fun t => ∫ x, normGradSqFun (S.family.metric t) (u t) x ∂μ t
  have hEcont : ContinuousOn energy (_root_.Set.Icc a b) :=
    (hu.continuousOn_integral_sq hS.smoothMetric).mono hcar
  have hDcont : ContinuousOn dirichlet (_root_.Set.Ioo a b) :=
    (hu.continuousOn_integral_normGradSqFun hS.smoothMetric).mono hreg
  obtain ⟨Av,hAv⟩ := (isCompact_Icc.prod isCompact_univ).bddAbove_image hV.norm
  let A := _root_.Max.max Av 0
  have hA : 0 ≤ A := le_max_right _ _
  have hAbound (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) (x : M) : |V t x| ≤ A := by
    exact (hAv ⟨(t,x),⟨ht,_root_.Set.mem_univ x⟩,rfl⟩).trans (le_max_left _ _)
  have hscalarCont : ContinuousOn (fun p : ℝ × M => S.scalar p.1 p.2) (_root_.Set.Icc a b ×ˢ _root_.Set.univ) :=
    hS.scalarCont.mono (_root_.Set.prod_mono hcar Subset.rfl)
  obtain ⟨Kr,hKr⟩ := (isCompact_Icc.prod isCompact_univ).bddAbove_image hscalarCont
  let K := _root_.Max.max Kr 0
  have hK : 0 ≤ K := le_max_right _ _
  have hKbound (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) (x : M) : S.scalar t x ≤ K :=
    (hKr ⟨(t,x),⟨ht,_root_.Set.mem_univ x⟩,rfl⟩).trans (le_max_left _ _)
  have hEnonneg (t : ℝ) : 0 ≤ energy t := _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hDnonneg (t : ℝ) : 0 ≤ dirichlet t := _root_.MeasureTheory.integral_nonneg fun x =>
    DifferentialGeometry.metric_inner_self_nonneg (S.family.metric t) x _
  have hEd (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) :=
    S.hasDerivAt_integral_sq_of_heat_potential hS hu (hreg ht) (hVsmooth t ht).continuous
  have hDd (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) :=
    hasDerivAt_integral_normGradSqFun_of_isHeatPotOn_of_finrank_eq_two S hS hdim hu
      (hreg ht) (hVsmooth t ht)
  have hbounds (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) (hpos : 0 < energy t) :
      (deriv dirichlet t * energy t - dirichlet t * deriv energy t) / (energy t)^2 ≤
        K * (dirichlet t / energy t) + A^2/2 ∧
      -(2 * (dirichlet t / energy t) + (2*A+K)) * energy t ≤ deriv energy t := by
    let g := S.family.metric t
    let : _root_.MeasureTheory.IsFiniteMeasure (μ t) := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
    have huSmooth := hu.sliceSmooth t (D.regular_subset (hreg ht))
    let lap := laplacian (LeviCivita g) g (u t)
    have hLap : ContMDiff I 𝓘(ℝ, ℝ) ∞ lap := contMDiff_laplacian_leviCivita g huSmooth
    let U : C(M, ℝ) := ⟨u t,huSmooth.continuous⟩
    let Z : C(M, ℝ) := ⟨fun x => -lap x,hLap.continuous.neg⟩
    let W : C(M, ℝ) := ⟨V t,(hVsmooth t ht).continuous⟩
    let R : C(M, ℝ) := ⟨S.scalar t,(metricScalar_smooth g).continuous⟩
    have hgreen : dirichlet t = ∫ x, Z x * U x ∂μ t :=
      integral_normGradSqFun_eq_integral_neg_laplacian_mul g huSmooth (HasCompactSupport.of_compactSpace _)
    have hD' : HasDerivAt dirichlet (-2 * (∫ x, (Z x)^2 ∂μ t) +
        2 * (∫ x, Z x * (W x * U x) ∂μ t)) t := by
      convert hDd t ht using 1
      dsimp only [Z,W,U,ContinuousMap.coe_mk]
      simp only [neg_sq,neg_mul,_root_.MeasureTheory.integral_neg]
      have heq : (∫ x, lap x * (V t x * u t x) ∂μ t) =
          ∫ x, V t x * u t x * lap x ∂μ t :=
        _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [heq]
      ring
    exact integral_frequency_differential_bounds (μ t) U Z W R rfl hpos hgreen (hDnonneg t)
      (hEd t ht) hD' hA (hAbound t (_root_.Set.Ioo_subset_Icc_self ht)) (hKbound t (_root_.Set.Ioo_subset_Icc_self ht))
  have hEzero : ∀ t ∈ _root_.Set.Icc a b, energy t = 0 := by
    apply eq_zero_of_terminal_zero_of_dirichlet_quotient_bounds hab hK (div_nonneg (sq_nonneg A) (by norm_num))
      hEcont hDcont (fun t _ => hEnonneg t) (fun t _ => hDnonneg t)
      (fun t ht => (hEd t ht).differentiableAt.hasDerivAt)
      (fun t ht => (hDd t ht).differentiableAt.hasDerivAt)
      (fun t ht hp => (hbounds t ht hp).1) (fun t ht hp => (hbounds t ht hp).2)
    simp only [energy,hterminal,zero_pow (by decide : 2 ≠ 0),_root_.MeasureTheory.integral_zero]
  intro t ht x
  let : _root_.MeasureTheory.IsFiniteMeasure (μ t) := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (S.family.metric t)
  let : (μ t).IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (S.family.metric t)
  have huc := (hu.sliceSmooth t (hcar ht)).continuous
  have hint : _root_.MeasureTheory.Integrable (fun x => (u t x)^2) (μ t) :=
    (huc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := (_root_.MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (u t x)) hint).mp (hEzero t ht)
  have hall := congrFun (MeasureTheory.Measure.eq_of_ae_eq hae (huc.pow 2) continuous_const) x
  exact sq_eq_zero_iff.mp hall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.heat_potential_eq_zero_of_terminal_eq_zero_on_surface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.heat_potential_eq_zero_of_terminal_eq_zero_on_surface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.heat_potential_eq_zero_of_terminal_eq_zero_on_surface ``Submission.DifferentialGeometry.PDE.RicciFlow.heat_potential_eq_zero_of_terminal_eq_zero_on_surface

end DifferentialGeometry.PDE.RicciFlow
