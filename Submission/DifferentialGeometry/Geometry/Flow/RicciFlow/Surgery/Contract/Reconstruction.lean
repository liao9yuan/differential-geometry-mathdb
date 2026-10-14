import Submission.DifferentialGeometry.Topology.Manifold.CollarFamily
import Submission.DifferentialGeometry.Topology.Manifold.RelativeCollar
import Submission.DifferentialGeometry.Topology.Manifold.ClosedOriented
import Submission.DifferentialGeometry.Topology.Manifold.SphereOrientation
import Submission.DifferentialGeometry.Topology.VanKampen.FullGroupoid
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def disjointBoundaryCollarFamily : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] (ι : Type u) [Fintype ι]
    (S : ι → Type u) [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)]
    (e : ∀ i, S i → X) (c : ∀ i, S i × ℝ → X),
    (∀ i, Topology.IsOpenEmbedding (c i)) →
    (∀ i s, c i (s, 0) = e i s) →
    (Pairwise fun i j => Disjoint (Set.range (e i)) (Set.range (e j))) →
    ∃ δ : ℝ, 0 < δ ∧
      Pairwise fun i j =>
        Disjoint (c i '' {q : S i × ℝ | |q.2| < δ}) (c j '' {q : S j × ℝ | |q.2| < δ})

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjointBoundaryCollarFamily

def relativeCollarUniqueness : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞),
    (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
    (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
    (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
      ∀ U : Set M, IsOpen U →
        (∃ ε : ℝ, 0 < ε ∧ ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε →
          c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) →
        ∃ δ : ℝ, 0 < δ ∧
          (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
            (p, t) ∈ c₀.source ∧ (p, t) ∈ c₁.source ∧
              c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) ∧
          ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
            (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
              Φ (c₀ (p, t)) = c₁ (p, t)) ∧
            Set.EqOn Φ id Uᶜ ∧ Set.EqOn Φ.symm id Uᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.relativeCollarUniqueness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.relativeCollarUniqueness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.relativeCollarUniqueness ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.relativeCollarUniqueness

def boundaryCollarGeometry : Prop :=
  disjointBoundaryCollarFamily.{u} ∧ relativeCollarUniqueness.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.boundaryCollarGeometry

structure OrientedBallEmbedding (U : Type u) [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace U ∞
  closedBall_subset_source : Metric.closedBall (0 : ThreeSpace) 2 ⊆ chart.source
  preserves_orientation : ∀ x, ∀ hx : x ∈ chart.source,
    Orientation.map (Fin 3)
      (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ chart hx)
        (by simp)).toLinearEquiv
      (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
        (NormedSpace.fromTangentSpace x).symm.toLinearEquiv).orientation) =
      o.orientation (chart x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedBallEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedBallEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedBallEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedBallEmbedding

def ballEmbeddingIsotopy : Prop :=
  ∀ (ι : Type u) [Fintype ι]
    (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
    (o : ManifoldOrientation ThreeModel U 3)
    (e e' : ι → OrientedBallEmbedding U o),
    (Pairwise fun i j =>
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) →
    (Pairwise fun i j =>
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) →
    ∃ H : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞,
      H 0 = Diffeomorph.refl ThreeModel U ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (H q.1).symm q.2) ∧
      ∃ K : Set U, IsCompact K ∧
        (∀ t, Set.EqOn (H t) (id : U → U) Kᶜ) ∧
        (∀ t, Set.EqOn (H t).symm (id : U → U) Kᶜ) ∧
        ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ i : ι, ∀ x : ThreeSpace,
          x ∈ Metric.closedBall 0 r → H 1 ((e i).chart x) = (e' i).chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy

def sphereDiffeomorphismIsotopyConnected : Prop :=
  ∀ f : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2,
    f.preservesOrientation (sphereOrientation 2 (by norm_num))
      (sphereOrientation 2 (by norm_num)) →
    ∃ A : C(Set.Icc (0 : ℝ) 1 × Sphere 2, Sphere 2),
      (∀ y, A (⟨0, by constructor <;> norm_num⟩, y) = f y) ∧
      (∀ y, A (⟨1, by constructor <;> norm_num⟩, y) = y) ∧
      ∀ t, ∃ e : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2, ∀ y, e y = A (t, y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereDiffeomorphismIsotopyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereDiffeomorphismIsotopyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereDiffeomorphismIsotopyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereDiffeomorphismIsotopyConnected

def seifertVanKampenPushout : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U V : Set X),
    IsOpen U → IsOpen V → U ∪ V = Set.univ →
      DifferentialGeometry.Topology.VanKampen.fullGroupoidSquareIsPushoutStatement U V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.seifertVanKampenPushout

def geometricReconstructionBackground : Prop :=
  boundaryCollarGeometry.{u} ∧ ballEmbeddingIsotopy.{u} ∧
    sphereDiffeomorphismIsotopyConnected ∧ seifertVanKampenPushout.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.geometricReconstructionBackground

def ballEmbeddingAmbientIsotopy : Prop :=
  ∀ (ι : Type u) [Fintype ι]
    (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] [ConnectedSpace U]
    (o : ManifoldOrientation ThreeModel U 3)
    (e e' : ι → OrientedBallEmbedding U o),
    (Pairwise fun i j =>
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) →
    (Pairwise fun i j =>
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) →
    ∃ H : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞,
      H 0 = Diffeomorph.refl ThreeModel U ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
        (fun q : ℝ × U => (H q.1).symm q.2) ∧
      (∀ t, (H t).preservesOrientation o o) ∧
      ∃ K : Set U, IsCompact K ∧
        (∀ t, Set.EqOn (H t) (id : U → U) Kᶜ) ∧
        (∀ t, Set.EqOn (H t).symm (id : U → U) Kᶜ) ∧
        ∀ i : ι, ∀ x : ThreeSpace,
          x ∈ Metric.closedBall (0 : ThreeSpace) 2 → H 1 ((e i).chart x) = (e' i).chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientIsotopy

def ballEmbeddingAmbientDiffeomorphism : Prop :=
  ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    [IsManifold ThreeModel ∞ U] [ConnectedSpace U]
    (o : ManifoldOrientation ThreeModel U 3) (e e' : OrientedBallEmbedding U o),
    ∃ Φ : Diffeomorph ThreeModel ThreeModel U U ∞,
      Φ.preservesOrientation o o ∧
      ∀ x : ThreeSpace, x ∈ Metric.closedBall (0 : ThreeSpace) 2 →
        Φ (e.chart x) = e'.chart x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism

theorem ballEmbeddingIsotopy_of_ambientIsotopy
    (h : ballEmbeddingAmbientIsotopy.{u}) : ballEmbeddingIsotopy.{u} := by
  intro ι _ U _ _ _ _ _ o e e' he he'
  obtain ⟨H, h0, hc, hc', -, K, hK, hKe, hKe', hball⟩ := h ι U o e e' he he'
  refine ⟨H, h0, hc, hc', K, hK, hKe, hKe', 1, by norm_num, le_rfl, fun i x hx => ?_⟩
  exact hball i x (Metric.closedBall_subset_closedBall (by norm_num) hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy_of_ambientIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy_of_ambientIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy_of_ambientIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingIsotopy_of_ambientIsotopy

theorem ballEmbeddingAmbientDiffeomorphism_of_ambientIsotopy
    (h : ballEmbeddingAmbientIsotopy.{u}) : ballEmbeddingAmbientDiffeomorphism.{u} := by
  intro U _ _ _ _ o e e'
  have hd : Pairwise fun i j : PUnit =>
      Disjoint (((fun _ : PUnit => e) i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        (((fun _ : PUnit => e) j).chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    fun i j hij => (hij (Subsingleton.elim i j)).elim
  have hd' : Pairwise fun i j : PUnit =>
      Disjoint (((fun _ : PUnit => e') i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        (((fun _ : PUnit => e') j).chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    fun i j hij => (hij (Subsingleton.elim i j)).elim
  obtain ⟨H, -, -, -, hpres, -, -, -, -, hball⟩ :=
    h PUnit U o (fun _ : PUnit => e) (fun _ : PUnit => e') hd hd'
  exact ⟨H 1, hpres 1, fun x hx => hball PUnit.unit x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism_of_ambientIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism_of_ambientIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism_of_ambientIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballEmbeddingAmbientDiffeomorphism_of_ambientIsotopy


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
