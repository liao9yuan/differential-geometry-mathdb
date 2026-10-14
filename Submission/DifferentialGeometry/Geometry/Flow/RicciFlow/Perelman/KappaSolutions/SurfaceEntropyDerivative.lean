import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRicciAlgebra
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

local instance surfaceDerivativeMeasurable : MeasurableSpace M := borel M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeMeasurable ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeMeasurable
local instance surfaceDerivativeBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeBorel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeBorel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeBorel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivativeBorel

theorem surfaceArea_hasDerivAt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t : Real} (ht : t ∈ D.regular) :
    HasDerivAt (fun s => surfaceArea (S.family.metric s))
      (-totalScalarCurvature (S.family.metric t)) t := by
  have hv := compact_ricciFlow_volumeVariation_on_regular S hS
    (fun _ _ => (1 : Real)) contMDiffOn_const ht
  have hsource :
      (fun s : Real => ∫ _x : M, (1 : Real)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s))) =
      fun s : Real => surfaceArea (S.family.metric s) := by
    funext s
    simp only [_root_.MeasureTheory.integral_const, smul_eq_mul, mul_one, surfaceArea]
  have hvalue :
      (∫ x : M, deriv (fun _ : Real => (1 : Real)) t - S.scalar t x * 1
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) =
      -totalScalarCurvature (S.family.metric t) := by
    simp only [deriv_const, mul_one, zero_sub, _root_.MeasureTheory.integral_neg,
      totalScalarCurvature, SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family]
  rw [hsource, hvalue] at hv
  exact hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceArea_hasDerivAt

section SurfaceEvolution

variable [I.Boundaryless]

omit [CompactSpace M] in
theorem surfaceScalar_hasDerivAt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2) {t : Real} (ht : t ∈ D.regular) (x : M) :
    HasDerivAt (fun s => S.scalar s x)
      (ΔG (I := I) (S.family.metric t) ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x +
        (S.scalar t x) ^ 2) t := by
  have he : HasDerivAt (fun s => S.scalar s x)
      (laplacianAt (I := I) (flowG S) t (S.scalar t) x +
        2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)) t :=
    ((scalar_curvature_evolution S hS) (⟨t, ht⟩ : D.RegularTime) x).hasDerivAt
      (D.regular_mem_nhds ht)
  have hlap : laplacianAt (I := I) (flowG S) t (S.scalar t) x =
      ΔG (I := I) (S.family.metric t) ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x :=
    laplacianAt_eq_delta (I := I) (flowG S) t (scalarSmoothOfSolution S t) rfl x
  have hricci : S.ricci t x = metricRicciAt (I := I) (S.family.metric t) x := by
    simpa only [SolutionOn.ricci, SolutionOn.family, SolutionFamily.ricciAt] using
      SolutionFamily.ricci_apply S.base t x
  have hreaction :
      2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) =
        (S.scalar t x) ^ 2 := by
    rw [hricci]
    exact two_mul_metricRicci_normSq_eq_scalar_sq_of_finrank_two
      (S.family.metric t) hdim x
  exact he.congr_deriv (congrArg₂ (fun a b : Real => a + b) hlap hreaction)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalar_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalar_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalar_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalar_hasDerivAt

theorem totalScalarCurvature_hasDerivAt_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2) {t : Real} (ht : t ∈ D.regular) :
    HasDerivAt (fun s => totalScalarCurvature (S.family.metric s)) 0 t := by
  have hjoint : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
      (fun p : Real × M => S.scalar p.1 p.2) (D.regular ×ˢ Set.univ) :=
    (scalar_joint S hS).of_le (by decide)
  have hv := compact_ricciFlow_volumeVariation_on_regular S hS S.scalar hjoint ht
  let R : C^∞⟮I, M; Real⟯ := ⟨S.scalar t, scalarSmoothOfSolution S t⟩
  have hvalue :
      (∫ x, deriv (fun s : Real => S.scalar s x) t - S.scalar t x * S.scalar t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) = 0 := by
    calc
      (∫ x, deriv (fun s : Real => S.scalar s x) t - S.scalar t x * S.scalar t x
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) =
          ∫ x, ΔG (I := I) (S.family.metric t) R x
            ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)) := by
        apply _root_.MeasureTheory.integral_congr_ae
        refine Eventually.of_forall (fun x => ?_)
        change deriv (fun s : Real => S.scalar s x) t -
          S.scalar t x * S.scalar t x = ΔG (I := I) (S.family.metric t) R x
        rw [(surfaceScalar_hasDerivAt S hS hdim ht x).deriv]
        change ΔG (I := I) (S.family.metric t) R x + (S.scalar t x) ^ 2 -
          S.scalar t x * S.scalar t x = ΔG (I := I) (S.family.metric t) R x
        ring
      _ = 0 := integral_divergence_eq_zero_of_compact (I := I)
        (S.family.metric t) (gradG (I := I) (S.family.metric t) R)
  exact hv.congr_deriv hvalue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_hasDerivAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_hasDerivAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_hasDerivAt_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.totalScalarCurvature_hasDerivAt_zero

omit [CompactSpace M] [I.Boundaryless] in
private theorem surfaceDerivative_log_smooth
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun x : M => Real.log (metricScalarAt (I := I) g x)) := by
  intro x
  exact (Real.contDiffAt_log.2 (hpositive x).ne').comp_contMDiffAt
    (x := x) ((metricScalar_smooth g) x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_log_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_log_smooth target :: scope.openDecls } }

private theorem surfaceDerivative_log_green
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    (∫ x, Real.log (R x) * ΔG (I := I) g ⟨R, metricScalar_smooth g⟩ x ∂μ) =
      -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  have hlog := surfaceDerivative_log_smooth g hpositive
  have hg := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) g hlog (metricScalar_smooth g) (HasCompactSupport.of_compactSpace _)
  have hpair :
      (∫ x, g.inner x (gradFun (I := I) g (fun y => Real.log (R y)) x)
        (gradFun (I := I) g R x) ∂μ) =
      ∫ x, normGradSqFun (I := I) g R x / R x ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    refine Eventually.of_forall (fun x => ?_)
    have hgrad : gradFun (I := I) g (fun y => Real.log (R y)) x =
        (R x)⁻¹ • gradFun (I := I) g R x := by
      simpa only [gradient_eq_gradFun] using gradientFun_log (I := I) g
        ((metricScalar_smooth g).mdifferentiableAt (by decide)) (hpositive x)
    change g.inner x (gradFun (I := I) g (fun y => Real.log (R y)) x)
        (gradFun (I := I) g R x) = normGradSqFun (I := I) g R x / R x
    rw [hgrad]
    simp only [map_smul, smul_apply, smul_eq_mul,
      normGradSqFun_def, div_eq_mul_inv]
    ring
  change (∫ x, g.inner x (gradFun (I := I) g (fun y => Real.log (R y)) x)
      (gradFun (I := I) g R x) ∂μ) =
    -(∫ x, Real.log (R x) * ΔG (I := I) g ⟨R, metricScalar_smooth g⟩ x ∂μ) at hg
  rw [hpair] at hg
  change (∫ x, Real.log (R x) * ΔG (I := I) g ⟨R, metricScalar_smooth g⟩ x ∂μ) =
    -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ)
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_log_green
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_log_green target :: scope.openDecls } }

private theorem surfaceDerivative_scalarLogIntegral_hasDerivAt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ s ∈ D.regular, ∀ x : M, 0 < S.scalar s x)
    {t : Real} (ht : t ∈ D.regular) :
    HasDerivAt
      (fun s : Real => ∫ x, S.scalar s x * Real.log (S.scalar s x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s)))
      (-(∫ x, normGradSqFun (I := I) (S.family.metric t) (S.scalar t) x /
          S.scalar t x ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) +
        ∫ x, (S.scalar t x) ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) t := by
  let g := S.family.metric t
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R : C^∞⟮I, M; Real⟯ := ⟨S.scalar t, scalarSmoothOfSolution S t⟩
  let volumeFinite : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hlogJoint : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => Real.log (S.scalar p.1 p.2)) (D.regular ×ˢ Set.univ) := by
    intro p hp
    exact ContDiffAt.comp_contMDiffWithinAt
      (x := p) (f := fun q : Real × M => S.scalar q.1 q.2)
      (Real.contDiffAt_log.2 (hpositive p.1 hp.1 p.2).ne')
      ((scalar_joint S hS) p hp)
  have hproductJoint : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
      (fun p : Real × M => S.scalar p.1 p.2 * Real.log (S.scalar p.1 p.2))
      (D.regular ×ˢ Set.univ) :=
    ((scalar_joint S hS).mul hlogJoint).of_le (by decide)
  have hv := compact_ricciFlow_volumeVariation_on_regular S hS
    (fun s x => S.scalar s x * Real.log (S.scalar s x)) hproductJoint ht
  have hpoint : ∀ x : M,
      deriv (fun s : Real => S.scalar s x * Real.log (S.scalar s x)) t -
        S.scalar t x * (S.scalar t x * Real.log (S.scalar t x)) =
      Real.log (R x) * ΔG (I := I) g R x + ΔG (I := I) g R x + (R x) ^ 2 := by
    intro x
    have hd := surfaceScalar_hasDerivAt S hS hdim ht x
    have hp := hd.fun_mul (hd.log (hpositive t ht x).ne')
    rw [hp.deriv]
    change (ΔG (I := I) g R x + (R x) ^ 2) * Real.log (R x) +
        R x * ((ΔG (I := I) g R x + (R x) ^ 2) / R x) -
        R x * (R x * Real.log (R x)) =
      Real.log (R x) * ΔG (I := I) g R x + ΔG (I := I) g R x + (R x) ^ 2
    have hRne : R x ≠ 0 := (hpositive t ht x).ne'
    field_simp [hRne]
    ring
  have hLcont : Continuous (ΔG (I := I) g R) := (Δ_g_contMDiff g R).continuous
  have hlogcont : Continuous (fun x : M => Real.log (R x)) :=
    (surfaceDerivative_log_smooth g (hpositive t ht)).continuous
  have hLint : _root_.MeasureTheory.Integrable (ΔG (I := I) g R) μ :=
    hLcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLogLint : _root_.MeasureTheory.Integrable (fun x : M => Real.log (R x) * ΔG (I := I) g R x) μ :=
    (hlogcont.mul hLcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR2int : _root_.MeasureTheory.Integrable (fun x : M => (R x) ^ 2) μ :=
    (R.contMDiff.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLapzero : (∫ x, ΔG (I := I) g R x ∂μ) = 0 :=
    integral_divergence_eq_zero_of_compact (I := I) g (gradG (I := I) g R)
  have hGreen : (∫ x, Real.log (R x) * ΔG (I := I) g R x ∂μ) =
      -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) :=
    surfaceDerivative_log_green g (hpositive t ht)
  have hvalue :
      (∫ x, deriv (fun s : Real => S.scalar s x * Real.log (S.scalar s x)) t -
          S.scalar t x * (S.scalar t x * Real.log (S.scalar t x)) ∂μ) =
      -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) + ∫ x, (R x) ^ 2 ∂μ := by
    calc
      (∫ x, deriv (fun s : Real => S.scalar s x * Real.log (S.scalar s x)) t -
          S.scalar t x * (S.scalar t x * Real.log (S.scalar t x)) ∂μ) =
          ∫ x, Real.log (R x) * ΔG (I := I) g R x +
            ΔG (I := I) g R x + (R x) ^ 2 ∂μ :=
        _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall hpoint)
      _ = _ := by
        have hsplit := _root_.MeasureTheory.integral_add (hLogLint.add hLint) hR2int
        simp only [Pi.add_apply] at hsplit
        rw [hsplit, _root_.MeasureTheory.integral_add hLogLint hLint,
          hLapzero, hGreen, add_zero]
  exact hv.congr_deriv hvalue

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_scalarLogIntegral_hasDerivAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_scalarLogIntegral_hasDerivAt target :: scope.openDecls } }

end SurfaceEvolution

section StaticEntropyAlgebra

variable [Nonempty M]

omit [CompleteSpace E] [IsManifold I 1 M] in
private theorem surfaceDerivative_area_positive
    (g : SmoothRiemannianMetric I M) : 0 < surfaceArea g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let volumeFinite : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let volumePositive : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact _root_.MeasureTheory.measureReal_univ_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_area_positive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_area_positive target :: scope.openDecls } }

theorem surfaceEntropy_eq_scalarLogIntegral_add
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x) :
    surfaceEntropy g =
      (∫ x, metricScalarAt (I := I) g x * Real.log (metricScalarAt (I := I) g x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        totalScalarCurvature g * Real.log (surfaceArea g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  let volumeFinite : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hRint : _root_.MeasureTheory.Integrable R μ :=
    (metricScalar_smooth g).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlog : Continuous (fun x : M => Real.log (R x)) := by
    apply Continuous.log (metricScalar_smooth g).continuous
    exact fun x => (hpositive x).ne'
  have hRlogint : _root_.MeasureTheory.Integrable (fun x : M => R x * Real.log (R x)) μ :=
    ((metricScalar_smooth g).continuous.mul hlog).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAne : surfaceArea g ≠ 0 := (surfaceDerivative_area_positive g).ne'
  change (∫ x, R x * Real.log (R x * surfaceArea g) ∂μ) =
    (∫ x, R x * Real.log (R x) ∂μ) + (∫ x, R x ∂μ) * Real.log (surfaceArea g)
  calc
    (∫ x, R x * Real.log (R x * surfaceArea g) ∂μ) =
        ∫ x, R x * Real.log (R x) + R x * Real.log (surfaceArea g) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      refine Eventually.of_forall (fun x => ?_)
      change R x * Real.log (R x * surfaceArea g) =
        R x * Real.log (R x) + R x * Real.log (surfaceArea g)
      rw [Real.log_mul (hpositive x).ne' hAne]
      ring
    _ = _ := by
      rw [_root_.MeasureTheory.integral_add hRlogint (hRint.mul_const _), _root_.MeasureTheory.integral_mul_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_eq_scalarLogIntegral_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_eq_scalarLogIntegral_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_eq_scalarLogIntegral_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_eq_scalarLogIntegral_add

private theorem surfaceDerivative_variance_identity
    (g : SmoothRiemannianMetric I M) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    (∫ x, (metricScalarAt (I := I) g x) ^ 2 ∂μ) -
        (totalScalarCurvature g) ^ 2 / surfaceArea g =
      ∫ x, (metricScalarAt (I := I) g x - meanScalarCurvature g) ^ 2 ∂μ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  let A := surfaceArea g
  let C := totalScalarCurvature g
  let r := meanScalarCurvature g
  let Q := ∫ x, (R x) ^ 2 ∂μ
  let volumeFinite : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hRint : _root_.MeasureTheory.Integrable R μ :=
    (metricScalar_smooth g).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR2int : _root_.MeasureTheory.Integrable (fun x : M => (R x) ^ 2) μ :=
    ((metricScalar_smooth g).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAne : A ≠ 0 := (surfaceDerivative_area_positive g).ne'
  have hExpand : (∫ x, (R x - r) ^ 2 ∂μ) = Q - 2 * r * C + A * r ^ 2 := by
    calc
      (∫ x, (R x - r) ^ 2 ∂μ) =
          ∫ x, (R x) ^ 2 - (2 * r) * R x + r ^ 2 ∂μ :=
        _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = Q - 2 * r * C + A * r ^ 2 := by
        have hsplit := _root_.MeasureTheory.integral_add (hR2int.sub (hRint.const_mul (2 * r)))
          (_root_.MeasureTheory.integrable_const (r ^ 2))
        simp only [Pi.sub_apply] at hsplit
        rw [hsplit,
          _root_.MeasureTheory.integral_sub hR2int (hRint.const_mul _), _root_.MeasureTheory.integral_const_mul,
          _root_.MeasureTheory.integral_const, smul_eq_mul]
        rfl
  change Q - C ^ 2 / A = ∫ x, (R x - r) ^ 2 ∂μ
  rw [hExpand]
  change Q - C ^ 2 / A = Q - 2 * (C / A) * C + A * (C / A) ^ 2
  field_simp [hAne]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_variance_identity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceDerivative_variance_identity target :: scope.openDecls } }

end StaticEntropyAlgebra

section EntropyDerivative

variable [I.Boundaryless] [Nonempty M]

theorem surfaceEntropy_hasDerivAt_first
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ s ∈ D.regular, ∀ x : M, 0 < S.scalar s x)
    {t : Real} (ht : t ∈ D.regular) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)
    let R := S.scalar t
    let r := meanScalarCurvature (S.family.metric t)
    HasDerivAt (fun s => surfaceEntropy (S.family.metric s))
      (-(∫ x, normGradSqFun (I := I) (S.family.metric t) R x / R x ∂μ) +
        ∫ x, (R x - r) ^ 2 ∂μ) t := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)
  let R := S.scalar t
  let r := meanScalarCurvature (S.family.metric t)
  let A := fun s : Real => surfaceArea (S.family.metric s)
  let C := fun s : Real => totalScalarCurvature (S.family.metric s)
  let J := fun s : Real => ∫ x, S.scalar s x * Real.log (S.scalar s x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s))
  let F := ∫ x, normGradSqFun (I := I) (S.family.metric t) R x / R x ∂μ
  let Q := ∫ x, (R x) ^ 2 ∂μ
  let V := ∫ x, (R x - r) ^ 2 ∂μ
  have hA : HasDerivAt A (-C t) t := surfaceArea_hasDerivAt S hS ht
  have hC : HasDerivAt C 0 t := totalScalarCurvature_hasDerivAt_zero S hS hdim ht
  have hJ : HasDerivAt J (-F + Q) t :=
    surfaceDerivative_scalarLogIntegral_hasDerivAt S hS hdim hpositive ht
  have hAne : A t ≠ 0 := (surfaceDerivative_area_positive (S.family.metric t)).ne'
  have hVariance : Q - (C t) ^ 2 / A t = V :=
    surfaceDerivative_variance_identity (S.family.metric t)
  have hsum := hJ.add (hC.mul (hA.log hAne))
  have hcoefficient : (-F + Q) + (0 * Real.log (A t) + C t * (-C t / A t)) =
      -F + V := by
    rw [← hVariance]
    ring
  have hsum' : HasDerivAt (fun s => J s + C s * Real.log (A s)) (-F + V) t :=
    hsum.congr_deriv hcoefficient
  have heventual : (fun s => surfaceEntropy (S.family.metric s)) =ᶠ[𝓝 t]
      (fun s => J s + C s * Real.log (A s)) := by
    filter_upwards [D.regular_isOpen.mem_nhds ht] with s hs
    exact surfaceEntropy_eq_scalarLogIntegral_add (S.family.metric s) (hpositive s hs)
  exact hsum'.congr_of_eventuallyEq heventual

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hasDerivAt_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hasDerivAt_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hasDerivAt_first ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_hasDerivAt_first

end EntropyDerivative

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
