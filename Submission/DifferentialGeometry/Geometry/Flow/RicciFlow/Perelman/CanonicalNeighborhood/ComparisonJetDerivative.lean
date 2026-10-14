import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
  {F : N → M} {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}

theorem MetricComparisonOn.hasDerivWithinAt_jet
    (c : MetricComparisonOn h g F U times order eps) {b : ℕ} {s : ℝ} {x : N}
    (hs : s ∈ times) (hx : x ∈ U)
    (hdiff : ∀ v : Fin 2 → TangentSpace I x,
      DifferentiableWithinAt ℝ (fun a => c.jet b a x v) times s) :
    HasDerivWithinAt (fun a => c.jet b a x) (c.jet (b + 1) s x) times s := by
  let basis := Module.finBasis ℝ (TangentSpace I x)
  apply tensor0S_hasDerivWithinAt_of_components basis
  intro slots
  change HasDerivWithinAt (fun a => c.jet b a x (fun j => basis (slots j)))
    (c.jet (b + 1) s x (fun j => basis (slots j))) times s
  rw [c.jet_succ b s hs x hx]
  exact (hdiff (fun j => basis (slots j))).hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.hasDerivWithinAt_jet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.hasDerivWithinAt_jet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.hasDerivWithinAt_jet ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.hasDerivWithinAt_jet

theorem MetricComparisonOn.jet_succ_eq_derivWithin
    (c : MetricComparisonOn h g F U times order eps) {b : ℕ} {s : ℝ} {x : N}
    (hs : s ∈ times) (hx : x ∈ U) (hunique : UniqueDiffWithinAt ℝ times s)
    (hdiff : ∀ v : Fin 2 → TangentSpace I x,
      DifferentiableWithinAt ℝ (fun a => c.jet b a x v) times s) :
    c.jet (b + 1) s x = derivWithin (fun a => c.jet b a x) times s :=
  ((c.hasDerivWithinAt_jet hs hx hdiff).derivWithin hunique).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_succ_eq_derivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_succ_eq_derivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_succ_eq_derivWithin ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_succ_eq_derivWithin

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
