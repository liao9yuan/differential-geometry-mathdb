import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance splittingNegativeTimeTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeTopology
local instance splittingNegativeTimeCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeCharted
local instance splittingNegativeTimeSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSmooth
local instance splittingNegativeTimeC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeC1
local instance splittingNegativeTimeT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeT2
local instance splittingNegativeTimeSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSigma
local instance splittingNegativeTimeInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeInhabited
local instance splittingNegativeTimeLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeLocallyPathConnected
local instance splittingNegativeTimeSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splittingNegativeTimeSemilocallySimplyConnected

def NegativeTimeUniversalCoverSplitting : Prop :=
  ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
    let _ : TopologicalSpace G.M := G.topology
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
    let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
    let _ : IsManifold (𝓡 2) 1 G.M :=
      IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
    let _ : T2Space G.M := G.t2
    let _ : SigmaCompactSpace G.M := G.sigmaCompact
    ConnectedSpace G.M ∧ SimplyConnectedSpace G.M ∧
      (∀ t : ℝ, t < 0 → MetricComplete (I := 𝓡 2) (G.atTime t)) ∧
      (∀ t : ℝ, t < 0 → ∀ y : G.M, 0 < G.S.scalar t y) ∧
      (∀ y : G.M, 0 < G.S.scalar 0 y) ∧
      ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ (t : ℝ), t < 0 → ∀ (y : G.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
            (G.S.family.metric t).inner y v w + a * c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NegativeTimeUniversalCoverSplitting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NegativeTimeUniversalCoverSplitting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NegativeTimeUniversalCoverSplitting ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NegativeTimeUniversalCoverSplitting


theorem ancient_fixed_universal_cover_product_of_negative_time_splitting
    (hconnected : ConnectedSpace F.M)
    (hcompleteF : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hsplit : NegativeTimeUniversalCoverSplitting (I := I) F) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G' : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G'.M := G'.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G'.M := G'.charted
      let _ : IsManifold (𝓡 2) ∞ G'.M := G'.smooth
      let _ : IsManifold (𝓡 2) 1 G'.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G'.M) (n := ∞) (by decide)
      let _ : T2Space G'.M := G'.t2
      let _ : SigmaCompactSpace G'.M := G'.sigmaCompact
      ConnectedSpace G'.M ∧ SimplyConnectedSpace G'.M ∧
        (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G'.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ y : G'.M, 0 < G'.S.scalar t y) ∧
        ∃ Phi' : (G'.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
          ∀ (t : ℝ), t ≤ 0 → ∀ (y : G'.M) (s : ℝ)
            (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
            (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi' (y, s))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (v, a))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (w, c)) =
              (G'.S.family.metric t).inner y v w + a * c := by
  obtain ⟨G, hconnG, hsimplyG, hcompleteG, hscalarG, hscalar0, Phi, hprod⟩ := hsplit
  exact ancient_fixed_universal_cover_product_of_negative_splitting
    F G Phi hconnected hcompleteF hconnG hsimplyG hcompleteG hscalarG hprod hscalar0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_splitting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_splitting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_splitting ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_splitting

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
