import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

def SpatialCanonicalWitness.HasMargins {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ}
    {x : M} (W : SpatialCanonicalWitness g eps C1 C2 x) (m : ℝ) : Prop :=
  ((∃ n, W.alternative = .neck n) ∨ ∃ c d, W.alternative = .cap c d) ∧
    (1 + m) / Real.sqrt (metricScalarAt g x) ≤ W.radius ∧
    riemannianBallOf (I := I3) g x ((1 + m) * W.radius) ⊆ W.domain.carrier ∧
    W.domain.carrier ⊆ riemannianBallOf (I := I3) g x ((2 - m) * W.radius) ∧
    ∀ c d, W.alternative = .cap c d →
      ∀ y ∈ c.tube, (10000 + m) / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins

variable {g : SmoothRiemannianMetric I3 M} {eps C1 C2 m : ℝ} {x : M}

theorem SpatialCanonicalWitness.HasMargins.enlarge_constants
    {W : SpatialCanonicalWitness g eps C1 C2 x} (h : W.HasMargins m)
    {C1' C2' : ℝ} (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    (W.enlargeConstants h1 h2).HasMargins m := by
  obtain ⟨hshape, hrad, hin, hout, hdeep⟩ := h
  have halt : (W.enlargeConstants h1 h2).alternative =
      W.alternative.monoConstant (zero_lt_one.trans_le W.one_le_comparison_constant) h2
        W.Q_pos.le := rfl
  refine ⟨?_, hrad, hin, hout, ?_⟩
  · rw [halt]
    rcases hshape with ⟨n, hn⟩ | ⟨c, d, hcd⟩
    · exact Or.inl ⟨n, by rw [hn]; rfl⟩
    · exact Or.inr ⟨c, d, by rw [hcd]; rfl⟩
  · intro c d heq
    rw [halt] at heq
    cases hW : W.alternative with
    | neck data =>
      rw [hW] at heq
      cases heq
    | cap data deep =>
      rw [hW] at heq
      change SpatialCanonicalAlternative.cap data deep = SpatialCanonicalAlternative.cap c d
        at heq
      cases heq
      exact hdeep _ _ hW
    | positive whole data sec =>
      rw [hW] at heq
      cases heq
    | round whole data =>
      rw [hW] at heq
      cases heq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins.enlarge_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins.enlarge_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins.enlarge_constants ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness.HasMargins.enlarge_constants

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
