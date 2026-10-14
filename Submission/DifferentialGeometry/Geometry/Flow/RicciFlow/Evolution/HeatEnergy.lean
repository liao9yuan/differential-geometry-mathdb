import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.LocalVariation
import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Equations.VolumeDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Submission.DifferentialGeometry.Geometry.Operator.LaplacianRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (compact_ricciFlow_volumeVariation_on_regular)
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.SolutionOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instCompleteSpace : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instCompleteSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.SolutionOn.instCompleteSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instMeasurableSpace : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instMeasurableSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.SolutionOn.instMeasurableSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instBorelSpace : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instBorelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.SolutionOn.instBorelSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instIsManifoldRealOfNatWithTopENat : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.instIsManifoldRealOfNatWithTopENat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.SolutionOn.instIsManifoldRealOfNatWithTopENat target :: scope.openDecls } }

theorem hasDerivAt_integral_sq_of_heat_potential
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {V u : ℝ → M → ℝ} (hu : IsHeatPotOn D (flowG S) V u)
    {t : ℝ} (ht : t ∈ D.regular) (hV : Continuous (V t)) :
    HasDerivAt
      (fun s : ℝ => ∫ x, (u s x) ^ 2
        ∂riemannianVolumeMeasure I M (S.family.metric s))
      (-2 * (∫ x, normGradSqFun (S.family.metric t) (u t) x
          ∂riemannianVolumeMeasure I M (S.family.metric t)) +
        ∫ x, (2 * V t x - S.scalar t x) * (u t x) ^ 2
          ∂riemannianVolumeMeasure I M (S.family.metric t)) t := by
  let g := S.family.metric t
  let μ := riemannianVolumeMeasure I M g
  let volumeFinite : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hut := hu.sliceSmooth t (D.regular_subset ht)
  let U : C^∞⟮I, M; ℝ⟯ := ⟨u t, hut⟩
  have hRcont : Continuous (S.scalar t) := (metricScalar_smooth g).continuous
  have hULint : _root_.MeasureTheory.Integrable (fun x : M => u t x * ΔG g U x) μ :=
    (hut.continuous.mul (Δ_g_contMDiff g U).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpotentialInt : _root_.MeasureTheory.Integrable
      (fun x : M => (2 * V t x - S.scalar t x) * (u t x) ^ 2) μ :=
    (((continuous_const.mul hV).sub hRcont).mul
      (hut.continuous.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hGreen : (∫ x, u t x * ΔG g U x ∂μ) =
      -(∫ x, normGradSqFun g (u t) x ∂μ) := by
    have h := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      g hut hut (HasCompactSupport.of_compactSpace _)
    change (∫ x, normGradSqFun g (u t) x ∂μ) =
      -(∫ x, u t x * ΔG g U x ∂μ) at h
    linarith
  have hpoint : ∀ x : M,
      deriv (fun s : ℝ => (u s x) ^ 2) t - S.scalar t x * (u t x) ^ 2 =
        2 * (u t x * ΔG g U x) + (2 * V t x - S.scalar t x) * (u t x) ^ 2 := by
    intro x
    have hd := (hu.equation t ht x).fun_pow 2
    rw [hd.deriv, laplacianAt_eq_delta (flowG S) t hut rfl x]
    change (2 : ℝ) * (u t x) ^ (2 - 1) *
        (ΔG g U x + V t x * u t x) - S.scalar t x * (u t x) ^ 2 = _
    ring
  have hv := compact_ricciFlow_volumeVariation_on_regular S hS
    (fun s x => (u s x) ^ 2) ((hu.jointSmooth.pow 2).of_le (by decide)) ht
  refine hv.congr_deriv ?_
  change (∫ x, deriv (fun s : ℝ => (u s x) ^ 2) t -
      S.scalar t x * (u t x) ^ 2 ∂μ) = _
  calc
    (∫ x, deriv (fun s : ℝ => (u s x) ^ 2) t -
        S.scalar t x * (u t x) ^ 2 ∂μ) =
        ∫ x, 2 * (u t x * ΔG g U x) +
          (2 * V t x - S.scalar t x) * (u t x) ^ 2 ∂μ :=
      _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall hpoint)
    _ = _ := by
      rw [_root_.MeasureTheory.integral_add (hULint.const_mul 2) hpotentialInt, _root_.MeasureTheory.integral_const_mul, hGreen]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_integral_sq_of_heat_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_integral_sq_of_heat_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_integral_sq_of_heat_potential ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.hasDerivAt_integral_sq_of_heat_potential

end DifferentialGeometry.PDE.RicciFlow.SolutionOn


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

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

theorem hasDerivAt_integral_normGradSqFun_of_finrank_eq_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2)
    {u : ℝ → M → ℝ} {ut : M → ℝ} {t : ℝ} (ht : t ∈ D.regular)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (D.regular ×ˢ _root_.Set.univ))
    (hut : ContMDiff I 𝓘(ℝ, ℝ) ∞ ut)
    (htime : ∀ x, HasDerivAt (fun s => u s x) (ut x) t) :
    HasDerivAt
      (fun s => ∫ x, normGradSqFun (I := I) (S.family.metric s) (u s) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s)))
      (-2 * ∫ x, ut x * laplacian (I := I)
          (LeviCivita (I := I) (S.family.metric t)) (S.family.metric t) (u t) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) t := by
  have hslice (s : ℝ) (hs : s ∈ D.regular) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (u s) := by
    intro x
    exact (hu.contMDiffAt
      ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨hs, _root_.Set.mem_univ x⟩)).comp x
        (contMDiffAt_const.prodMk contMDiffAt_id)
  have hswap := DifferentialGeometry.fixedBaseOnRegularity_of_timeDerivWithin
    (I := I) (timeSet := D.regular) (regularSet := {t}) (u := (_root_.Set.univ : Set M))
    (F := u) (Ft := fun _ => ut)
    (by intro s hs; rcases mem_singleton_iff.mp hs with rfl; exact ht)
    (by intro s hs; rcases mem_singleton_iff.mp hs with rfl
        exact D.regular_isOpen.mem_nhds ht)
    (by
      intro s hs x _
      rcases mem_singleton_iff.mp hs with rfl
      exact (hu.contMDiffAt
        ((D.regular_isOpen.prod isOpen_univ).mem_nhds ⟨ht, _root_.Set.mem_univ x⟩)).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (fun s hs x _ => (hslice s hs).mdifferentiable (by simp) x)
    (fun _ _ x _ => hut.mdifferentiable (by simp) x)
    (by intro s hs x; rcases mem_singleton_iff.mp hs with rfl
        exact (htime x).hasDerivWithinAt)
  have hgram := fun α i j => hS.smoothMetric.chartGramMatrix_contDiffOn
    (Set.Subset.rfl) α i j
  have hgrad := gradSq_joint (I := I) S.family.metric D.regular_isOpen hgram u hu
  have hfirst := first_var_joint (I := I) (M := M)
    (f := fun s x => (S.family.metric s).inner x
      (gradientFun (I := I) (S.family.metric s) (u s) x)
      (gradientFun (I := I) (S.family.metric s) (u s) x))
    D.regular_isOpen ht hgram hgrad
  change HasDerivAt
    (fun s => ∫ x, normGradSqFun (I := I) (S.family.metric s) (u s) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s))) _ t at hfirst
  have hpde (x : M) (v w : TangentSpace I x) :
      HasDerivAt (fun s => (S.family.metric s).inner x v w)
        (-2 * ricciTensor (I := I) (S.family.metric t) x v w) t := by
    have h := metricDerivAt S hS ⟨t, ht⟩ x v w
    change HasDerivAt _
      (-2 * metricRicciAt (I := I) (S.family.metric t) x (vec2 v w)) t at h
    simpa only [DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor] using h
  have htrace := traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow
    (I := I) S.family.metric hpde
  refine hfirst.congr_deriv ?_
  calc
    _ = ∫ x, 2 * (S.family.metric t).inner x
        (gradientFun (I := I) (S.family.metric t) ut x)
        (gradientFun (I := I) (S.family.metric t) (u t) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      have hdf (v : TangentSpace I x) :
          HasDerivAt (fun s => mvfderiv (I := I) (u s) x v)
            (mvfderiv (I := I) ut x v) t :=
        (hswap t (_root_.Set.mem_singleton t) x (_root_.Set.mem_univ x) v).hasDerivAt
          (D.regular_isOpen.mem_nhds ht)
      have hnorm := normGradSq_time (I := I) S.family.metric u ut (S.ricciAt t x)
        (metricDerivAt S hS ⟨t, ht⟩ x) hdf
      rw [hnorm.deriv, htrace x]
      change 2 * metricRicciAt (I := I) (S.family.metric t) x
          (fun a : Fin 2 => if a = 0 then _ else _) + _ + _ = _
      rw [metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two
        (S.family.metric t) hdim x, Tensor0SSpace.smul_apply, metricTensor0S_apply]
      simp only [ite_self, smul_eq_mul]
      ring
    _ = 2 * ∫ x, (S.family.metric t).inner x
        (gradientFun (I := I) (S.family.metric t) ut x)
        (gradientFun (I := I) (S.family.metric t) (u t) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)) :=
      _root_.MeasureTheory.integral_const_mul _ _
    _ = _ := by
      have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
        (I := I) (S.family.metric t) hut (hslice t ht) (HasCompactSupport.of_compactSpace _)
      change (∫ x, (S.family.metric t).inner x
          (gradientFun (I := I) (S.family.metric t) ut x)
          (gradientFun (I := I) (S.family.metric t) (u t) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) =
        -∫ x, ut x * ΔG (I := I) (S.family.metric t) ⟨u t, hslice t ht⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)) at hgreen
      rw [hgreen]
      simp_rw [laplacian_levi_eq (S.family.metric t) (hslice t ht)]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_finrank_eq_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_finrank_eq_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_finrank_eq_two ``Submission.DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_finrank_eq_two

end DifferentialGeometry.PDE.RicciFlow


noncomputable section

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem hasDerivAt_integral_normGradSqFun_of_isHeatPotOn_of_finrank_eq_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 2)
    {V u : ℝ → M → ℝ} (hu : IsHeatPotOn D (flowG S) V u)
    {t : ℝ} (ht : t ∈ D.regular)
    (hV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (V t)) :
    HasDerivAt
      (fun s => ∫ x, normGradSqFun (I := I) (S.family.metric s) (u s) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s)))
      (-2 * (∫ x, (laplacian (I := I)
          (LeviCivita (I := I) (S.family.metric t)) (S.family.metric t) (u t) x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) -
        2 * ∫ x, V t x * u t x * laplacian (I := I)
          (LeviCivita (I := I) (S.family.metric t)) (S.family.metric t) (u t) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) t := by
  let L : M → ℝ := laplacian (I := I)
    (LeviCivita (I := I) (S.family.metric t)) (S.family.metric t) (u t)
  let μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)
  have husmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) :=
    hu.sliceSmooth t (D.regular_subset ht)
  have hL : ContMDiff I 𝓘(ℝ, ℝ) ∞ L :=
    contMDiff_laplacian_leviCivita (S.family.metric t) husmooth
  have hut : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => L x + V t x * u t x) :=
    hL.add (hV.mul husmooth)
  have htime (x : M) :
      HasDerivAt (fun s => u s x) (L x + V t x * u t x) t :=
    hu.equation t ht x
  have hLL : _root_.MeasureTheory.Integrable (fun x => (L x) ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (S.family.metric t) (hL.continuous.pow 2) (HasCompactSupport.of_compactSpace _)
  have hVuL : _root_.MeasureTheory.Integrable (fun x => V t x * u t x * L x) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (S.family.metric t) ((hV.continuous.mul husmooth.continuous).mul hL.continuous)
      (HasCompactSupport.of_compactSpace _)
  have hsplit : (∫ x, (L x + V t x * u t x) * L x ∂μ) =
      (∫ x, (L x) ^ 2 ∂μ) + ∫ x, V t x * u t x * L x ∂μ := by
    calc
      _ = ∫ x, (L x) ^ 2 + V t x * u t x * L x ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := _root_.MeasureTheory.integral_add hLL hVuL
  refine (hasDerivAt_integral_normGradSqFun_of_finrank_eq_two S hS hdim ht
    hu.jointSmooth hut htime).congr_deriv ?_
  change -2 * (∫ x, (L x + V t x * u t x) * L x ∂μ) =
    -2 * (∫ x, (L x) ^ 2 ∂μ) - 2 * ∫ x, V t x * u t x * L x ∂μ
  rw [hsplit]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_isHeatPotOn_of_finrank_eq_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_isHeatPotOn_of_finrank_eq_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_isHeatPotOn_of_finrank_eq_two ``Submission.DifferentialGeometry.PDE.RicciFlow.hasDerivAt_integral_normGradSqFun_of_isHeatPotOn_of_finrank_eq_two

end DifferentialGeometry.PDE.RicciFlow
