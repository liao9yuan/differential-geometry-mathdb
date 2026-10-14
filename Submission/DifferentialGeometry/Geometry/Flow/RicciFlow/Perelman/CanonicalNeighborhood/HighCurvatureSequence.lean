import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

noncomputable def highCurvatureInterval {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) : RealTimeInterval :=
  RealTimeInterval.closed (-(t i * S.scalar (t i) (x i))) 0
    (by
      have h1 : 0 < t i * S.scalar (t i) (x i) := mul_pos (htpos i) (hpos i)
      linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem highCurvatureInterval_carrier {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).carrier =
      Set.Icc (-(t i * S.scalar (t i) (x i))) 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem highCurvatureInterval_regular {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).regular =
      Set.Ioo (-(t i * S.scalar (t i) (x i))) 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular

omit [T2Space M] [SigmaCompactSpace M] in
theorem highCurvatureInterval_carrier_subset {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).carrier ⊆
      (parabolicInterval (RealTimeInterval.closedOpen 0 T hT) (t i)
        (S.scalar (t i) (x i)) (htmem i)).carrier := by
  intro s hs
  have hQ : 0 < S.scalar (t i) (x i) := hpos i
  have htT : t i < T := (htmem i).2
  have hlow : 0 ≤ t i + s / S.scalar (t i) (x i) := by
    have h1 : -(t i * S.scalar (t i) (x i)) ≤ s := hs.1
    have h2 : -t i ≤ s / S.scalar (t i) (x i) := by
      rw [le_div_iff₀ hQ]
      nlinarith [h1]
    linarith
  have hhigh : t i + s / S.scalar (t i) (x i) < T := by
    have h1 : s ≤ 0 := hs.2
    have h2 : s / S.scalar (t i) (x i) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hQ.le
    linarith
  simpa only [parabolicInterval_carrier, parabolicTime, Set.mem_ofPred_eq,
    Set.mem_Ico] using ⟨hlow, hhigh⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier_subset

omit [T2Space M] [SigmaCompactSpace M] in
theorem highCurvatureInterval_regular_subset {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (i : ℕ) :
    (highCurvatureInterval hT S x t htpos hpos i).regular ⊆
      (parabolicInterval (RealTimeInterval.closedOpen 0 T hT) (t i)
        (S.scalar (t i) (x i)) (htmem i)).regular := by
  intro s hs
  have hQ : 0 < S.scalar (t i) (x i) := hpos i
  have htT : t i < T := (htmem i).2
  have hlow : 0 < t i + s / S.scalar (t i) (x i) := by
    have h1 : -(t i * S.scalar (t i) (x i)) < s := hs.1
    have h2 : -t i < s / S.scalar (t i) (x i) := by
      rw [lt_div_iff₀ hQ]
      nlinarith [h1]
    linarith
  have hhigh : t i + s / S.scalar (t i) (x i) < T := by
    have h1 : s < 0 := hs.2
    have h2 : s / S.scalar (t i) (x i) < 0 := div_neg_of_neg_of_pos h1 hQ
    linarith
  simpa only [parabolicInterval_regular, parabolicTime, Set.mem_ofPred_eq,
    Set.mem_Ioo] using ⟨hlow, hhigh⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular_subset

noncomputable def highCurvatureFlowSequence {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) : FlowSequence.{u} where
  interval i := highCurvatureInterval hT S x t htpos hpos i
  term i :=
    { M := M
      basepoint := x i
      S := (parabolicSolution (I := I3) (M := M) S (t i)
        (S.scalar (t i) (x i)) (hpos i) (htmem i)).timeRestrict
          (highCurvatureInterval hT S x t htpos hpos i)
      isSolution := isSolutionOn_timeRestrict (I := I3) (M := M)
        (parabolicSolution_isSolutionOn (I := I3) (M := M) S hS (t i)
          (S.scalar (t i) (x i)) (hpos i) (htmem i))
        (highCurvatureInterval_carrier_subset hT S x t htpos hpos htmem i)
        (highCurvatureInterval_regular_subset hT S x t htpos hpos htmem i) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence

@[simp] theorem highCurvatureFlowSequence_interval {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    (highCurvatureFlowSequence hT S hS x t htmem htpos hpos).interval i =
      highCurvatureInterval hT S x t htpos hpos i :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_interval

@[simp] theorem highCurvatureFlowSequence_basepoint {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).basepoint =
      x i :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_basepoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_basepoint

@[simp] theorem highCurvatureFlowSequence_metric {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : ℕ) :
    ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term i).S.base.metric =
      rescaledMetric (I := I3) S (t i) (S.scalar (t i) (x i)) (hpos i) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence_metric

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
