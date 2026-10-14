import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.Functional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.Filter _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {M : Type*}

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem weightedIBP
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hlap :
      _root_.MeasureTheory.Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hpotential⟩ x)
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hgrad :
      _root_.MeasureTheory.Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          g.inner x
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hpotential⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hpotential⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
      (DifferentialGeometry.Geometry.Operator.ΔG
          (I := I) g ⟨_, hpotential⟩ x -
        g.inner x
          ((DifferentialGeometry.Geometry.Operator.gradG
            (I := I) g ⟨_, hpotential⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((DifferentialGeometry.Geometry.Operator.gradG
            (I := I) g ⟨_, hpotential⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  apply expWeightedIBP_of_baseIntegral_zero
    (mu := riemannianVolumeMeasure (I := I) (M := M) g)
    (potential := potential)
    (lapPotential :=
      DifferentialGeometry.Geometry.Operator.ΔG
        (I := I) g ⟨_, hpotential⟩)
    (gradPotentialNormSq := fun x : M =>
      g.inner x
        ((DifferentialGeometry.Geometry.Operator.gradG
          (I := I) g ⟨_, hpotential⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((DifferentialGeometry.Geometry.Operator.gradG
          (I := I) g ⟨_, hpotential⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
  · exact hmeas
  · simpa [expNegPotentialDensity] using
      DifferentialGeometry.Integral.DivergenceTheorem.expNegIBP
        (I := I) g hpotential hlap hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedIBP then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.weightedIBP"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedIBP ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.weightedIBP

omit [TopologicalSpace M] in
theorem bracket_eq_closed_of_ibp [MeasurableSpace M]
    (mu : _root_.MeasureTheory.Measure M)
    (scalarCurvature lapPotential gradPotentialNormSq potential : M -> Real)
    (hscalar_int :
      _root_.MeasureTheory.Integrable scalarCurvature
        (expNegPotentialWeightedMeasure mu potential))
    (hlap_int :
      _root_.MeasureTheory.Integrable lapPotential
        (expNegPotentialWeightedMeasure mu potential))
    (hgrad_int :
      _root_.MeasureTheory.Integrable gradPotentialNormSq
        (expNegPotentialWeightedMeasure mu potential))
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure mu potential) = 0) :
    (∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
      ∂(expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, fFunctionalClosedBracket scalarCurvature lapPotential x
        ∂(expNegPotentialWeightedMeasure mu potential) := by
  let μw := expNegPotentialWeightedMeasure mu potential
  have hdiff :
      (∫ x, lapPotential x ∂μw) =
        ∫ x, gradPotentialNormSq x ∂μw := by
    have hsub :
        (∫ x, (lapPotential x - gradPotentialNormSq x) ∂μw) =
          (∫ x, lapPotential x ∂μw) -
            ∫ x, gradPotentialNormSq x ∂μw := by
      exact _root_.MeasureTheory.integral_sub hlap_int hgrad_int
    rw [hsub] at hibp
    linarith
  calc
    (∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x ∂μw)
        =
      ∫ x, scalarCurvature x + gradPotentialNormSq x ∂μw := by
        rfl
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, gradPotentialNormSq x ∂μw := by
        exact _root_.MeasureTheory.integral_add hscalar_int hgrad_int
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, lapPotential x ∂μw := by
        rw [hdiff]
    _ =
      ∫ x, scalarCurvature x + lapPotential x ∂μw := by
        exact (_root_.MeasureTheory.integral_add hscalar_int hlap_int).symm
    _ =
      ∫ x, fFunctionalClosedBracket scalarCurvature lapPotential x ∂μw := by
        rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.bracket_eq_closed_of_ibp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.bracket_eq_closed_of_ibp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.bracket_eq_closed_of_ibp ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.bracket_eq_closed_of_ibp

theorem weightedGreen
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
        DifferentialGeometry.Geometry.Operator.ΔG
          (I := I) g ⟨_, hq⟩ x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        q x *
          (-DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x +
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let gradSq : M -> Real := fun x =>
    g.inner x
      ((DifferentialGeometry.Geometry.Operator.gradG
        (I := I) g ⟨_, hpotential⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((DifferentialGeometry.Geometry.Operator.gradG
        (I := I) g ⟨_, hpotential⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hq⟩ x)
    hmeas]
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      q x *
        (-DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hpotential⟩ x + gradSq x))
    hmeas]
  calc
    ∫ x,
        expNegPotentialDensity potential x *
          DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hq⟩ x ∂μ =
      ∫ x,
        q x *
          (expNegPotentialDensity potential x *
            (-DifferentialGeometry.Geometry.Operator.ΔG
                (I := I) g ⟨_, hpotential⟩ x + gradSq x)) ∂μ := by
      simpa [μ, expNegPotentialDensity, gradSq] using
        DifferentialGeometry.Integral.DivergenceTheorem.expNegGreen
          (I := I) g hpotential hq
    _ =
      ∫ x,
        expNegPotentialDensity potential x *
          (q x *
            (-DifferentialGeometry.Geometry.Operator.ΔG
                (I := I) g ⟨_, hpotential⟩ x + gradSq x)) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedGreen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.weightedGreen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedGreen ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.weightedGreen

theorem weightedDivZero
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace : M -> Real}
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdiv :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
            (I := I) g X x =
          expNegPotentialDensity potential x * weightedDivergenceTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := weightedDivergenceTrace) hmeas]
  calc
    ∫ x, expNegPotentialDensity potential x * weightedDivergenceTrace x ∂μ =
        ∫ x, DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
          (I := I) g X x ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (hdiv x).symm
    _ = 0 := by
      simpa [μ] using
        DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact
          (I := I) g X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem expNegPotentialDensity_contMDiff
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) :
    ContMDiff I 𝓘(Real, Real) ∞ (expNegPotentialDensity potential) := by
  change ContMDiff I 𝓘(Real, Real) ∞ (fun x => Real.exp (-(potential x)))
  have h := Real.contDiff_exp.contMDiff.comp hpotential.neg
  convert h using 1
  · with_reducible_and_instances rfl
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_contMDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_contMDiff

omit [FiniteDimensional ℝ E] in
theorem tangentSectionAction_expNeg
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
        (I := I) X (expNegPotentialDensity potential) x =
      -expNegPotentialDensity potential x *
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
          (I := I) X potential x := by
  have hmf :=
    DifferentialGeometry.Integral.DivergenceTheorem.mfderiv_exp_neg_toLinearMap
      (I := I) (f := potential) (x := x)
      (hpotential.mdifferentiableAt (by simp))
  unfold DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
    expNegPotentialDensity
  change
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(potential y))) x (X x)) =
      -Real.exp (-(potential x)) *
        (show ℝ from mfderiv I 𝓘(ℝ, ℝ) potential x (X x))
  have happly := congrArg
    (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L (X x)) hmf
  change
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(potential y))) x (X x)) =
      -Real.exp (-(potential x)) *
        (show ℝ from mfderiv I 𝓘(ℝ, ℝ) potential x (X x)) at happly
  exact happly

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.tangentSectionAction_expNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.tangentSectionAction_expNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.tangentSectionAction_expNeg ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.tangentSectionAction_expNeg

def connTraceVec
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
  DifferentialGeometry.Integral.DivergenceTheorem.smoothSmul
    (I := I) (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceVec ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceVec

theorem connTraceDivEq
    [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hdivTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∀ x : M,
      DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
          (I := I) g
          (connTraceVec (I := I) hpotential traceVec) x =
        expNegPotentialDensity potential x * weightedDivergenceTrace x := by
  intro x
  rw [connTraceVec]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_smoothSmul
    (I := I) g (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec x]
  rw [hdivTrace x]
  rw [tangentSectionAction_expNeg (I := I) traceVec hpotential x]
  rw [hactionTrace x, hweighted x]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceDivEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceDivEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceDivEq ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.connTraceDivEq

theorem weightedDivZero_of_connTrace
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdivTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  exact weightedDivZero (I := I) g
    (connTraceVec (I := I) hpotential traceVec) hmeas
    (connTraceDivEq (I := I) g hpotential traceVec hdivTrace
      hactionTrace hweighted)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero_of_connTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero_of_connTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero_of_connTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.weightedDivZero_of_connTrace

theorem weighted_grad_zero
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q) :
    ∫ x,
        (DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hq⟩ x -
          g.inner x
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hq⟩) x)
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hpotential⟩) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (ENNReal.continuous_ofReal.comp
      (expNegPotentialDensity_contMDiff (I := I) hpotential).continuous).aemeasurable
  exact weightedDivZero_of_connTrace (I := I) g hpotential
    (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨_, hq⟩)
    hmeas
    (fun x =>
      (DifferentialGeometry.Geometry.Operator.Δ_g_def
        (I := I) g ⟨_, hq⟩ x).symm)
    (fun x =>
      DifferentialGeometry.Geometry.Operator.tangentSectionAction_eq_inner_grad_g
        (I := I) g ⟨_, hpotential⟩
        (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨_, hq⟩) x)
    (fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_grad_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_grad_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_grad_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_grad_zero

theorem shiftIntEq
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q shiftedTrace potentialVariation metricVariationTrace :
      M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hq⟩ x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    ∫ x, shiftedTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x -
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  calc
    ∫ x, shiftedTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hq⟩ x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply _root_.MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hshift
    _ = ∫ x,
        q x *
          (-DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x +
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      exact weightedGreen (I := I) g hpotential hq hmeas
    _ = ∫ x,
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x -
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply _root_.MeasureTheory.integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      dsimp
      rw [hqeq x]
      unfold expWeightedMeasureVariationFactor
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.shiftIntEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.shiftIntEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.shiftIntEq ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.shiftIntEq

theorem expWeightedMeasureIntegral_hasDerivAt_at
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {potentialPath phiPath : Real -> M -> Real}
    {s0 : Real}
    {potentialVariation metricVariationTrace phiVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (hphi_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => phiPath s x)
          (phiVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x * phiPath s x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (phiPath s0) phiVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 := by
  have hvol :=
    volume_variation_formula_at
      (I := I) (M := M) G
      (f := fun s : Real => fun x : M =>
        expNegPotentialDensity (potentialPath s) x * phiPath s x)
      (t₀ := s0) hmetric_regularity hintegrand_regularity
  refine hvol.congr_deriv ?_
  apply _root_.MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hdens :=
    expNegPotentialDensity_hasDerivAt
      (M := M) (potentialPath := potentialPath)
      (potentialVariation := potentialVariation)
      hpotential_deriv x
  have hprod :
      HasDerivAt
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        (-(potentialVariation x) *
            expNegPotentialDensity (potentialPath s0) x * phiPath s0 x +
          expNegPotentialDensity (potentialPath s0) x * phiVariation x)
        s0 :=
    hdens.mul (hphi_deriv x)
  have hderiv := hprod.deriv
  change
    deriv
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0 +
      1 / 2 * traceTimeDerivMetricAt (I := I) G s0 x *
        (expNegPotentialDensity (potentialPath s0) x * phiPath s0 x) =
    expWeightedIntegralVariationIntegrand
      (potentialPath s0) potentialVariation metricVariationTrace
      (phiPath s0) phiVariation x
  rw [hderiv, htrace x]
  unfold expWeightedIntegralVariationIntegrand
    expWeightedMeasureVariationFactor
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureIntegral_hasDerivAt_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureIntegral_hasDerivAt_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureIntegral_hasDerivAt_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureIntegral_hasDerivAt_at

def fFunctionalBracketVariation
    (scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + gradPotentialNormSqVariation x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracketVariation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracketVariation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracketVariation ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracketVariation

omit [TopologicalSpace M] in
theorem fFunctionalBracket_hasDerivAt
    {scalarCurvaturePath gradPotentialNormSqPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x)
      (fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hgrad_deriv x)
  change HasDerivAt
    (fun s : Real => scalarCurvaturePath s x + gradPotentialNormSqPath s x)
    (scalarCurvatureVariation x + gradPotentialNormSqVariation x) s0
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket_hasDerivAt

omit [TopologicalSpace M] in
theorem closedBracket_deriv
    {scalarCurvaturePath lapPotentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        fFunctionalClosedBracket (scalarCurvaturePath s)
          (lapPotentialPath s) x)
      (fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hlap_deriv x)
  change HasDerivAt
    (fun s : Real => scalarCurvaturePath s x + lapPotentialPath s x)
    (scalarCurvatureVariation x + lapPotentialVariation x) s0
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.closedBracket_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.closedBracket_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.closedBracket_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.closedBracket_deriv

theorem fFunctionalBaseIntegral_hasDerivAt_at
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      fFunctionalBracket (scalarCurvaturePath s)
        (gradPotentialNormSqPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation)
    hpotential_deriv
    (fFunctionalBracket_hasDerivAt
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (gradPotentialNormSqPath := gradPotentialNormSqPath)
      (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (gradPotentialNormSqVariation := gradPotentialNormSqVariation)
      hscalar_deriv hgrad_deriv)
    htrace hmetric_regularity hintegrand_regularity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBaseIntegral_hasDerivAt_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBaseIntegral_hasDerivAt_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBaseIntegral_hasDerivAt_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBaseIntegral_hasDerivAt_at

theorem closedBase_deriv
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalClosedBracket (scalarCurvaturePath s0)
            (lapPotentialPath s0))
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      fFunctionalClosedBracket (scalarCurvaturePath s)
        (lapPotentialPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation)
    hpotential_deriv
    (closedBracket_deriv
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (lapPotentialPath := lapPotentialPath) (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (lapPotentialVariation := lapPotentialVariation)
      hscalar_deriv hlap_deriv)
    htrace hmetric_regularity hintegrand_regularity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.closedBase_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.closedBase_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.closedBase_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.closedBase_deriv

omit [TopologicalSpace M] in
theorem FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    [MeasurableSpace M]
    {muPath : Real -> _root_.MeasureTheory.Measure M}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 firstVariation : Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (muPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(muPath s))
    (hbase :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalBracket (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) x
            ∂(muPath s))
        firstVariation s0) :
    FFunctionalHasFirstVariationAt muPath scalarCurvaturePath
      gradPotentialNormSqPath potentialPath s0 firstVariation := by
  unfold FFunctionalHasFirstVariationAt fFunctionalAlong
  exact hbase.congr_of_eventuallyEq hbase_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt

theorem FFunctionalHasFirstVariationAt_of_volumeVariation
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (volumeMeasureFamily (I := I) (M := M) G s)
          (scalarCurvaturePath s) (gradPotentialNormSqPath s)
          (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    FFunctionalHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G)
      scalarCurvaturePath gradPotentialNormSqPath potentialPath s0
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) := by
  exact FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    hbase_eq
    (fFunctionalBaseIntegral_hasDerivAt_at
      (I := I) (M := M) G
      hscalar_deriv hgrad_deriv hpotential_deriv htrace hmetric_regularity
      hintegrand_regularity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_volumeVariation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_volumeVariation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_volumeVariation ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt_of_volumeVariation

end Geometry

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
