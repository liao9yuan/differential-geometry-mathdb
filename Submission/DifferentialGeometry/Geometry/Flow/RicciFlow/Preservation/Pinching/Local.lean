import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicci.HeatEquation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Quotient.Evolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Reaction.Hamilton
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.TraceFreeRicci.Evolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Evolution.Solution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Evolution.Intrinsic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Estimate.Pinching

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.Manifold _root_.ContDiff

variable {M : Type*}

def CurvatureEigenvaluesOrdered
    (lambda mu nu : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), nu t x ≤ mu t x ∧ mu t x ≤ lambda t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureEigenvaluesOrdered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureEigenvaluesOrdered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureEigenvaluesOrdered ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureEigenvaluesOrdered

def RicciPinchingPreservedOn
    (lambda mu nu : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M), lambda t x ≤ C * (nu t x + mu t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedOn ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedOn

def RicciPinchingPreservedInequalityOn
    (lambda mu nu : Real -> M -> Real) (C : Real) : Prop :=
  RicciPinchingPreservedOn lambda mu nu C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedInequalityOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedInequalityOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedInequalityOn ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciPinchingPreservedInequalityOn

def LogPinchingDerivativeNonpositiveOn
    (lambda mu nu : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    0 < lambda t x ∧ 0 < mu t x + nu t x ->
      (mu t x ^ 2 * (nu t x - lambda t x) +
        nu t x ^ 2 * (mu t x - lambda t x)) /
          (lambda t x * (nu t x + mu t x)) ≤ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.LogPinchingDerivativeNonpositiveOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.LogPinchingDerivativeNonpositiveOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.LogPinchingDerivativeNonpositiveOn ``Submission.DifferentialGeometry.PDE.RicciFlow.LogPinchingDerivativeNonpositiveOn

def LogLambdaOverMuPlusNuDerivativeFormulaOn
    (lambda mu nu : Real -> M -> Real) : Prop :=
  LogPinchingDerivativeNonpositiveOn lambda mu nu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.LogLambdaOverMuPlusNuDerivativeFormulaOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.LogLambdaOverMuPlusNuDerivativeFormulaOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.LogLambdaOverMuPlusNuDerivativeFormulaOn ``Submission.DifferentialGeometry.PDE.RicciFlow.LogLambdaOverMuPlusNuDerivativeFormulaOn

def RicciLowerBoundFromPinchingOn
    (ricciLower scalar : Real -> M -> Real) (beta : Real) : Prop :=
  ∀ (t : Real) (x : M), 2 * beta ^ 2 * scalar t x ≤ ricciLower t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciLowerBoundFromPinchingOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciLowerBoundFromPinchingOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciLowerBoundFromPinchingOn ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciLowerBoundFromPinchingOn

def PinchingDecayWeightOn
    (weight : Real -> M -> Real) (delta : Real) : Prop :=
  ∀ (t : Real) (x : M), 0 < delta ∧ 0 ≤ weight t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PinchingDecayWeightOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PinchingDecayWeightOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PinchingDecayWeightOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PinchingDecayWeightOn

def RicciPinchingImprovesOn
    (lambda mu nu weight : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    (lambda t x - nu t x) / (nu t x + mu t x) ≤
      C * weight t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciPinchingImprovesOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciPinchingImprovesOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciPinchingImprovesOn ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciPinchingImprovesOn

def PinchingImprovesFunctionEvolutionOn
    (f rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), f t x ≤ rhs t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PinchingImprovesFunctionEvolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PinchingImprovesFunctionEvolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PinchingImprovesFunctionEvolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PinchingImprovesFunctionEvolutionOn

def HamiltonTracefreePinchingEstimateOn
    (tracefreeRmNormSq scalar weight : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    tracefreeRmNormSq t x / scalar t x ^ 2 ≤ C * weight t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonTracefreePinchingEstimateOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonTracefreePinchingEstimateOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonTracefreePinchingEstimateOn ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonTracefreePinchingEstimateOn

def pinchingP (lambda mu nu : Real) : Real :=
  lambda ^ 2 * (mu - nu) ^ 2 +
    mu ^ 2 * (lambda - nu) ^ 2 +
    nu ^ 2 * (lambda - mu) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchingP then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchingP"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchingP ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchingP

def PinchingPFormulaOn
    (lambda mu nu P : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    P t x = pinchingP (lambda t x) (mu t x) (nu t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PinchingPFormulaOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PinchingPFormulaOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PinchingPFormulaOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PinchingPFormulaOn

theorem pinchingP_formula
    (lambda mu nu : Real -> M -> Real) :
    PinchingPFormulaOn lambda mu nu
      (fun t x => pinchingP (lambda t x) (mu t x) (nu t x)) := by
  intro t x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.pinchingP_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.pinchingP_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.pinchingP_formula ``Submission.DifferentialGeometry.PDE.RicciFlow.pinchingP_formula

abbrev PAlphaOverQBetaFormulaOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Prop :=
  QuotientEvolutionOn (I := I) (D := D) G
    phi psi phiHeat psiHeat alpha beta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PAlphaOverQBetaFormulaOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PAlphaOverQBetaFormulaOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PAlphaOverQBetaFormulaOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PAlphaOverQBetaFormulaOn

def TracefreeRmPinchingEvolutionInequalityOn
    (f scalar Q : Real -> M -> Real) (epsilon : Real) : Prop :=
  ∀ (t : Real) (x : M),
    0 < scalar t x -> f t x ≤ Q t x + epsilon * scalar t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TracefreeRmPinchingEvolutionInequalityOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TracefreeRmPinchingEvolutionInequalityOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TracefreeRmPinchingEvolutionInequalityOn ``Submission.DifferentialGeometry.PDE.RicciFlow.TracefreeRmPinchingEvolutionInequalityOn

def ScalarEvolutionEigenvalueFormulaOn
    (scalar lambda mu nu rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    rhs t x =
      scalar t x ^ 2 +
        2 * (lambda t x * mu t x + lambda t x * nu t x + mu t x * nu t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEigenvalueFormulaOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEigenvalueFormulaOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEigenvalueFormulaOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarEvolutionEigenvalueFormulaOn

theorem ricci_pinching_preserved
    (lambda mu nu : Real -> M -> Real) (C : Real)
    (hode :
      CurvatureEigenvaluesOrdered lambda mu nu →
        (∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) →
          RicciPinchingPreservedOn lambda mu nu C)
    (hordered : CurvatureEigenvaluesOrdered lambda mu nu)
    (hinit : ∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) :
    RicciPinchingPreservedOn lambda mu nu C :=
  hode hordered hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricci_pinching_preserved then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricci_pinching_preserved"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricci_pinching_preserved ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_pinching_preserved

theorem ricci_lower_bound_of_pinching
    (lambda mu nu ricciLower scalar : Real -> M -> Real)
    (C beta : Real)
    (hbound :
      RicciPinchingPreservedOn lambda mu nu C →
        beta > 0 →
          RicciLowerBoundFromPinchingOn ricciLower scalar beta)
    (hpinch : RicciPinchingPreservedOn lambda mu nu C)
    (hbeta : beta > 0) :
    RicciLowerBoundFromPinchingOn ricciLower scalar beta :=
  hbound hpinch hbeta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricci_lower_bound_of_pinching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricci_lower_bound_of_pinching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricci_lower_bound_of_pinching ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_lower_bound_of_pinching

theorem ricci_pinching_improves
    (lambda mu nu : Real -> M -> Real)
    (hpositiveRicciInitial : Prop)
    (hinit : hpositiveRicciInitial)
    (himprove :
      hpositiveRicciInitial →
        ∃ C delta : Real, ∃ weight : Real -> M -> Real,
          0 < C ∧ 0 < delta ∧ delta < 1 ∧
          PinchingDecayWeightOn weight delta ∧
          RicciPinchingImprovesOn lambda mu nu weight C) :
    ∃ C delta : Real, ∃ weight : Real -> M -> Real,
      0 < C ∧ 0 < delta ∧ delta < 1 ∧
      PinchingDecayWeightOn weight delta ∧
      RicciPinchingImprovesOn lambda mu nu weight C :=
  himprove hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricci_pinching_improves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricci_pinching_improves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricci_pinching_improves ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_pinching_improves

theorem hamilton_tracefree_pinching_of_eigenvalue_pinching
    (lambda mu nu tracefreeRmNormSq scalar weight : Real -> M -> Real)
    (C : Real)
    (hconvert :
      RicciPinchingImprovesOn lambda mu nu weight C →
        HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C)
    (hpinch : RicciPinchingImprovesOn lambda mu nu weight C) :
    HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C :=
  hconvert hpinch

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.hamilton_tracefree_pinching_of_eigenvalue_pinching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.hamilton_tracefree_pinching_of_eigenvalue_pinching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.hamilton_tracefree_pinching_of_eigenvalue_pinching ``Submission.DifferentialGeometry.PDE.RicciFlow.hamilton_tracefree_pinching_of_eigenvalue_pinching

theorem palpha_over_qbeta_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [IsManifold I 1 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      phiLap (t : Real) x =
        DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G (t : Real) (phi (t : Real))
          x)
    (hpsiLap : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      psiLap (t : Real) x =
        DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G (t : Real) (psi (t : Real))
          x)
    (hphiDiff : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime
      D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime
      D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    PAlphaOverQBetaFormulaOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta :=
  quotHeat (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat alpha beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.palpha_over_qbeta_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.palpha_over_qbeta_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.palpha_over_qbeta_formula ``Submission.DifferentialGeometry.PDE.RicciFlow.palpha_over_qbeta_formula

theorem tracefree_rm_pinching_evolution
    (f scalar Q : Real -> M -> Real) (epsilon : Real)
    (hineq : ∀ t x,
      0 < scalar t x -> f t x ≤ Q t x + epsilon * scalar t x) :
    TracefreeRmPinchingEvolutionInequalityOn f scalar Q epsilon :=
  hineq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tracefree_rm_pinching_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tracefree_rm_pinching_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tracefree_rm_pinching_evolution ``Submission.DifferentialGeometry.PDE.RicciFlow.tracefree_rm_pinching_evolution

end DifferentialGeometry.PDE.RicciFlow
