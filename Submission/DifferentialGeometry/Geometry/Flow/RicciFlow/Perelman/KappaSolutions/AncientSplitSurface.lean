import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SplitSurfaceKappaSolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSimplyConnectedSurface

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance ancientSplitSurfaceSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceSphereDimension target :: scope.openDecls } }

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientSplitSurfaceBaseTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseTopology
local instance ancientSplitSurfaceBaseCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseCharted
local instance ancientSplitSurfaceBaseSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSmooth
local instance ancientSplitSurfaceBaseC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseC1
local instance ancientSplitSurfaceBaseT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseT2
local instance ancientSplitSurfaceBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSigma
local instance ancientSplitSurfaceBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseInhabited
local instance ancientSplitSurfaceBaseLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseLocallyPathConnected
local instance ancientSplitSurfaceBaseSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplitSurfaceBaseSemilocallySimplyConnected

theorem ancientKappa_null_plane_split_surface {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G.M := G.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
      let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
      let _ : IsManifold (𝓡 2) 1 G.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
      let _ : T2Space G.M := G.t2
      let _ : SigmaCompactSpace G.M := G.sigmaCompact
      SimplyConnectedSpace G.M ∧ IsAncientKappaSolution (I := 𝓡 2) (kappa / 2) G ∧
      ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ (t : ℝ), t ≤ 0 → ∀ (y : G.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
            (G.S.family.metric t).inner y v w + a * c := by
  let _ : ConnectedSpace F.M := hF.connected
  have hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C := by
    obtain ⟨C, _, hRm⟩ := ancientKappa_rmNormSqBounded F hdim hF
    intro a b _ hb
    refine ⟨(Real.sqrt 3 * C) ^ 2, sq_nonneg _, ?_⟩
    intro t ht x
    exact hRm t (by simpa using ht.2.trans hb) x
  obtain ⟨G, hG⟩ := ancient_fixed_universal_cover_product_of_null_plane F hdim
    hF.connected (fun t ht => hF.complete t (by simpa using ht))
    (fun t ht => hF.nonnegativeCurvatureOperator t (by simpa using ht)) hbounded hF.notFlat
    t₀ ht₀ x₀ v₀ w₀ hplane hnull
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  obtain ⟨hconnectedG, hsimplyG, hcompleteG, hpositiveG, Phi, hproduct⟩ := hG
  refine ⟨G, hsimplyG, ?_, Phi, hproduct⟩
  exact splitSurface_toIsAncientKappaSolution F G Phi hproduct hF hdim
    hconnectedG hcompleteG hpositiveG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_split_surface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_split_surface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_split_surface ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_split_surface

theorem ancientKappa_null_plane_fixed_round_cylinder {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ (t : ℝ), t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
          (v w : TangentSpace (𝓡 2) x) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, c)) =
            (2 * (T - t)) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
              x v w + a * c := by
  obtain ⟨G, hG⟩ := ancientKappa_null_plane_split_surface
    F hF hdim t₀ ht₀ x₀ v₀ w₀ hplane hnull
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  obtain ⟨hsimplyG, hkappaG, Phi, hproduct⟩ := hG
  have hdimG : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  let _ : CompactSpace G.M := ancientKappaSurface_compact G hkappaG hdimG
  let T := surfaceArea (G.S.family.metric 0) / totalScalarCurvature (G.S.family.metric 0)
  obtain ⟨hT, e, hround⟩ :=
    ancientKappaSurface_simplyConnected_fixed_round_diffeomorph G hkappaG hdimG hsimplyG
  let eP : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ G.M × ℝ :=
    e.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  let Psi := eP.trans Phi
  have heP (x : SphereTwo) (s : ℝ) (v : TangentSpace (𝓡 2) x) (a : ℝ) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) eP (x, s) (v, a) =
        (mfderiv (𝓡 2) (𝓡 2) e x v, a) := by
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Prod.map (e : SphereTwo → G.M) (id : ℝ → ℝ)) (x, s) (v, a) = _
    rw [mfderiv_prodMap (e.mdifferentiable (by decide) x) mdifferentiableAt_id,
      mfderiv_id]
    rfl
  have hPsi (x : SphereTwo) (s : ℝ) (v : TangentSpace (𝓡 2) x) (a : ℝ) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (e x, s)
          (mfderiv (𝓡 2) (𝓡 2) e x v, a) := by
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I
      ((Phi : G.M × ℝ → UniversalCover F.M) ∘ (eP : SphereTwo × ℝ → G.M × ℝ))
      (x, s) (v, a) = _
    rw [mfderiv_comp_apply (x, s) (Phi.mdifferentiable (by decide) (eP (x, s)))
      (eP.mdifferentiable (by decide) (x, s)) (v, a), heP]
    rfl
  refine ⟨T, hT, Psi, ?_⟩
  intro t ht x s v w a c
  change (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner
    (Phi (e x, s))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, c)) = _
  rw [hPsi, hPsi, hproduct t ht, hround t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_fixed_round_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_fixed_round_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_fixed_round_cylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_fixed_round_cylinder

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
