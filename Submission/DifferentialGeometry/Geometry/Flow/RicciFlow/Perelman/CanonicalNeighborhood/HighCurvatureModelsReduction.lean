import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupLimitSelection

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
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

def BlowupLimitModelFrontier {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) : Prop :=
  let _ := hS
  ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
    ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
      (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
      ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupLimitModelFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupLimitModelFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupLimitModelFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupLimitModelFrontier

def BlowupAtHighCurvatureFrontier {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (o : TangentOrientationSection M) : Prop :=
  ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
    (∀ i, t i ∈ Set.Ico 0 T) →
    Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
      Nonempty (BlowupLimit S o kappa x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupAtHighCurvatureFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupAtHighCurvatureFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupAtHighCurvatureFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BlowupAtHighCurvatureFrontier

def BufferedCanonicalPullbackFrontier : Prop :=
  ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
      ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
          (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
          IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
          Set.Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          OrientedWitness S o delta kappa x t →
            Nonempty (CanonicalWitness S eps C1 C2 x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonicalPullbackFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonicalPullbackFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonicalPullbackFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.BufferedCanonicalPullbackFrontier

theorem bufferedCanonicalPullbackFrontier_iff_kappaUniformCanonicalClassification :
    BufferedCanonicalPullbackFrontier.{u} ↔
      kappaUniformCanonicalClassification.{u} :=
  ⟨fun hpb => kappaUniformCanonicalClassification_of_buffered_canonical_pullback hpb,
    fun hclass => buffered_canonical_pullback_of_classification hclass⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_iff_kappaUniformCanonicalClassification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_iff_kappaUniformCanonicalClassification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_iff_kappaUniformCanonicalClassification ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_iff_kappaUniformCanonicalClassification

def QuantifiedWitnessCore (eps kappa : ℝ) : Prop :=
  ∃ C1 C2 delta : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < delta ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
      (o : TangentOrientationSection M) (x : M) (t : ℝ),
      OrientedWitness S o delta kappa x t →
        Nonempty (CanonicalWitness S eps C1 C2 x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.QuantifiedWitnessCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.QuantifiedWitnessCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.QuantifiedWitnessCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.QuantifiedWitnessCore

omit [SigmaCompactSpace M] in
theorem quantifiedWitnessCore_holds (eps kappa : ℝ) (h : eps = 1) :
    QuantifiedWitnessCore.{u} eps kappa := by
  subst h
  have h1 : (1 : ℝ) ≤ 1 := le_rfl
  have h2 : (1 : ℝ) ≤ 1 := le_rfl
  have h3 : (0 : ℝ) < 1 := one_pos
  refine ⟨1, 1, 1, h1, h2, h3, ?_⟩
  intro M _ _ _ _ _ D S o x t hw
  have hempty := isEmpty_orientedWitness_of_one_le (eps := 1) (kappa := kappa) S o x t le_rfl
  exact (hempty.false hw).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quantifiedWitnessCore_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quantifiedWitnessCore_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quantifiedWitnessCore_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.quantifiedWitnessCore_holds

theorem bufferedCanonicalPullbackFrontier_of_windowedCanonicalPullback
    (h : windowedCanonicalPullback.{u}) : BufferedCanonicalPullbackFrontier.{u} :=
  buffered_canonical_pullback_of_windowedCanonicalPullback h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_of_windowedCanonicalPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_of_windowedCanonicalPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_of_windowedCanonicalPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.bufferedCanonicalPullbackFrontier_of_windowedCanonicalPullback

omit [SigmaCompactSpace M] in
theorem maximal_point_singularity_model_of_blowupLimitModelFrontier
    [CompactSpace M] [ConnectedSpace M] [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    (h : BlowupLimitModelFrontier.{u} hT S hS o) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 :=
  h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.maximal_point_singularity_model_of_blowupLimitModelFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.maximal_point_singularity_model_of_blowupLimitModelFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.maximal_point_singularity_model_of_blowupLimitModelFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.maximal_point_singularity_model_of_blowupLimitModelFrontier

omit [T2Space M] [SigmaCompactSpace M] in
theorem arbitrary_high_curvature_blowup_of_blowupAtHighCurvatureFrontier
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (o : TangentOrientationSection M)
    (h : BlowupAtHighCurvatureFrontier.{u} hT S o) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ico 0 T) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        Nonempty (BlowupLimit S o kappa x t) :=
  h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.arbitrary_high_curvature_blowup_of_blowupAtHighCurvatureFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.arbitrary_high_curvature_blowup_of_blowupAtHighCurvatureFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.arbitrary_high_curvature_blowup_of_blowupAtHighCurvatureFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.arbitrary_high_curvature_blowup_of_blowupAtHighCurvatureFrontier

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
