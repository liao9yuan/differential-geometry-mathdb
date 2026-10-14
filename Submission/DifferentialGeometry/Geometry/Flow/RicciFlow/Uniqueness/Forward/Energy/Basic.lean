import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.DifferenceFields
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricDeriv
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.LocalVariation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]

section MovingNorm

def movingReact0S (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (Q : Tensor0SSpace 2 I x) (W : Tensor0SSpace s I x) : Real :=
  ricReactionContract
    (basisInvMetric (I := I) g x (Module.finBasis Real (TangentSpace I x)))
    (fun i j =>
      Q (fun a : Fin 2 =>
        if a = 0 then Module.finBasis Real (TangentSpace I x) i
        else Module.finBasis Real (TangentSpace I x) j))
    (fun I0 =>
      tensor0SComponent (I := I) W
        (fun i => Module.finBasis Real (TangentSpace I x) i) I0)
    (fun J0 =>
      tensor0SComponent (I := I) W
        (fun i => Module.finBasis Real (TangentSpace I x) i) J0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.movingReact0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.movingReact0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.movingReact0S ``Submission.DifferentialGeometry.PDE.RicciFlow.movingReact0S

omit [T2Space M] in
theorem normSq0S_moving_deriv {s : Nat} {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace 2 I x)
    (T : Real → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hT : ∀ v : Fin s → TangentSpace I x,
      HasDerivAt (fun r : Real => T r v) (Tdot v) t) :
    HasDerivAt (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (movingReact0S (I := I) (g t) x s Q (T t) +
        2 * inner0S (I := I) (g t) x s Tdot (T t)) t := by
  classical
  let basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  let gInv : Real →
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun r =>
    basisInvMetric (I := I) (g r) x basis
  let ric :
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i j =>
    Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let gInvDt :
      Fin (Module.finrank Real (TangentSpace I x)) →
      Fin (Module.finrank Real (TangentSpace I x)) → Real := fun i j =>
    -(∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j)
  let Tdt : (Fin s → Fin (Module.finrank Real (TangentSpace I x))) → Real := fun I0 =>
    tensor0SComponent (I := I) Tdot (fun i => basis i) I0
  have hinvAll (r : Real) :
      MetricInverseInBasis (I := I) (g r) x basis (gInv r) := by
    simpa [gInv] using basisInvMetric_isInverse (I := I) (g r) x basis
  have hgInv (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) Set.univ t := by
    simpa [gInv, gInvDt, ric] using
      (basisInv_time (I := I) g
        (fun p q => (-2 : Real) * ric p q) basis
        (fun p q => by simpa [ric] using hg (basis p) (basis q)) i j)
  have hTcomp (I0 : Fin s → Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) Set.univ t :=
    (hT fun a => basis (I0 a)).hasDerivWithinAt
  have hTdot (I0 : Fin s → Fin (Module.finrank Real (TangentSpace I x))) :
      tensor0SComponent (I := I) Tdot (fun i => basis i) I0 = Tdt I0 := rfl
  have hflow (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      gInvDt i j = 2 * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
    have hterm :
        (∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j) =
          ∑ p, ∑ q, (-2 : Real) * (gInv t i p * gInv t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor :
        (∑ p, ∑ q, (-2 : Real) * (gInv t i p * gInv t j q * ric p q)) =
          (-2 : Real) * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gInvDt]
    rw [hterm, hfactor]
    ring
  have hbase :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I) (s := s) (u := Set.univ) (t := t)
      g gInv gInvDt ric T Tdt Tdot basis hinvAll hgInv hTcomp hTdot hflow
  exact hbase.hasDerivAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.normSq0S_moving_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.normSq0S_moving_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.normSq0S_moving_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.normSq0S_moving_deriv

end MovingNorm

section Carriers

def metricDiffDot (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    Tensor0SSpace 2 I x :=
  (-2 : Real) •
    (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricDiffDot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricDiffDot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricDiffDot ``Submission.DifferentialGeometry.PDE.RicciFlow.metricDiffDot

omit [T2Space M] in
theorem metricDifference_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M) {x : M} {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hPDE₂ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (v : Fin 2 → TangentSpace I x) :
    HasDerivAt (fun r : Real => metricDiffAt (I := I) (g₁ r) (g₂ r) x v)
      (metricDiffDot (I := I) g₁ g₂ t x v) t := by
  classical
  have hslots :
      (fun a : Fin 2 => if a = 0 then v 0 else v 1) = v := by
    funext a
    fin_cases a <;> simp
  have hsub := (hPDE₁ (v 0) (v 1)).sub (hPDE₂ (v 0) (v 1))
  have hfun :
      (fun r : Real => metricDiffAt (I := I) (g₁ r) (g₂ r) x v) =
        fun r : Real => (g₁ r).inner x (v 0) (v 1) - (g₂ r).inner x (v 0) (v 1) := by
    funext r
    exact metricDiffAt_apply (I := I) (g₁ r) (g₂ r) x v
  have hval :
      metricDiffDot (I := I) g₁ g₂ t x v =
        (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
            (fun a : Fin 2 => if a = 0 then v 0 else v 1) -
          (-2 : Real) * metricRicciAt (I := I) (g₂ t) x
            (fun a : Fin 2 => if a = 0 then v 0 else v 1) := by
    have hsmul :
        metricDiffDot (I := I) g₁ g₂ t x v =
          (-2 : Real) •
            ((metricRicciAt (I := I) (g₁ t) x -
                metricRicciAt (I := I) (g₂ t) x) v) :=
      Tensor0SSpace.smul_apply (I := I) 2 x (-2 : Real)
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) v
    have hdiff :
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) v =
          metricRicciAt (I := I) (g₁ t) x v - metricRicciAt (I := I) (g₂ t) x v :=
      Tensor0SSpace.sub_apply (I := I) 2 x
        (metricRicciAt (I := I) (g₁ t) x) (metricRicciAt (I := I) (g₂ t) x) v
    rw [hsmul, hdiff, hslots]
    simp only [smul_eq_mul]
    ring
  rw [hfun, hval]
  exact hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricDifference_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricDifference_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricDifference_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.metricDifference_hasDerivAt

end Carriers

section EnergyDefinitions

variable [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }
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

def forwardUniqueDensity (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    Real :=
  metricDiffSq (I := I) (g₁ t) (g₂ t) x + connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x +
    rmDiffSq (I := I) (g₁ t) (g₂ t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensity

def forwardUniqueEnergy (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) : Real :=
  ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy ``Submission.DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy

def forwardUniqueDensityDot
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (t : Real) (x : M) : Real :=
  (movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x)) +
  (movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
      (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
      (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x)) +
  (movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensityDot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensityDot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensityDot ``Submission.DifferentialGeometry.PDE.RicciFlow.forwardUniqueDensityDot

def forwardUniqueRate
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (t : Real) : Real :=
  ∫ x, forwardUniqueDensityDot (I := I) g₁ g₂ Adot Sdot t x +
      (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
        forwardUniqueDensity (I := I) g₁ g₂ t x
    ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forwardUniqueRate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forwardUniqueRate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forwardUniqueRate ``Submission.DifferentialGeometry.PDE.RicciFlow.forwardUniqueRate

end EnergyDefinitions

section Energy

variable [CompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_2 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_3 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_3 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry_3 target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] in
theorem density_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    {x : M} {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hPDE₂ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ v : Fin 3 → TangentSpace I x,
      HasDerivAt (fun r : Real => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Adot t x v) t)
    (hS : ∀ v : Fin 4 → TangentSpace I x,
      HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Sdot t x v) t) :
    HasDerivAt (fun r : Real => forwardUniqueDensity (I := I) g₁ g₂ r x)
      (forwardUniqueDensityDot (I := I) g₁ g₂ Adot Sdot t x) t := by
  have hh :
      HasDerivAt (fun r : Real => metricDiffSq (I := I) (g₁ r) (g₂ r) x)
        (movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
            (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
          2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
            (metricDiffAt (I := I) (g₁ t) (g₂ t) x)) t :=
    normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
      (fun r => metricDiffAt (I := I) (g₁ r) (g₂ r) x)
      (metricDiffDot (I := I) g₁ g₂ t x) hPDE₁
      (metricDifference_hasDerivAt (I := I) g₁ g₂ hPDE₁ hPDE₂)
  have hA' :
      HasDerivAt (fun r : Real => connectionDifferenceSq (I := I) (g₁ r) (g₂ r) x)
        (movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
            (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
          2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
            (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x)) t :=
    normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
      (fun r => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x) (Adot t x) hPDE₁ hA
  have hS' :
      HasDerivAt (fun r : Real => rmDiffSq (I := I) (g₁ r) (g₂ r) x)
        (movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
            (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
          2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
            (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)) t :=
    normSq0S_moving_deriv (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x)
      (fun r => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x) (Sdot t x) hPDE₁ hS
  exact (hh.add hA').add hS'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.density_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.density_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.density_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.density_hasDerivAt

theorem forwardUniqueEnergy_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    {U : Set Real} {t : Real} (hU : IsOpen U) (ht : t ∈ U)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (U ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdens : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (U ×ˢ (Set.univ : Set M)))
    (hPDE₁ : ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hPDE₂ : ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : Real => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Adot t x v) t)
    (hS : ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (Sdot t x v) t) :
    HasDerivAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂)
      (forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t) t := by
  have hbase := first_var_joint (I := I) (M := M) hU ht hgram hdens
  have hval :
      (∫ x, (deriv (fun s : Real => forwardUniqueDensity (I := I) g₁ g₂ s x) t +
            (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
              forwardUniqueDensity (I := I) g₁ g₂ t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)) =
        forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t := by
    simp only [forwardUniqueRate]
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [(density_hasDerivAt (I := I) g₁ g₂ Adot Sdot
      (hPDE₁ x) (hPDE₂ x) (hA x) (hS x)).deriv]
  exact hbase.congr_deriv hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.forwardUniqueEnergy_hasDerivAt

end Energy

end DifferentialGeometry.PDE.RicciFlow

end
