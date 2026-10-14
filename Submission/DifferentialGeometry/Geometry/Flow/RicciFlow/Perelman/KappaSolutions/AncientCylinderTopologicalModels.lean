import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.CylinderDescent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckRecentering
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalQuotient

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

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance ancientCylinderModelsSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSphereDimension target :: scope.openDecls } }

private theorem ancientCylinderModels_antipodal (x : SphereTwo) :
    sphereDiffeo (n := 2) (LinearIsometryEquiv.neg ℝ : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
        x = -x := by
  apply Subtype.ext
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModels_antipodal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModels_antipodal target :: scope.openDecls } }

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientCylinderModelsTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsTopology
local instance ancientCylinderModelsCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsCharted
local instance ancientCylinderModelsSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSmooth
local instance ancientCylinderModelsInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsInhabited
local instance ancientCylinderModelsT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsT2
local instance ancientCylinderModelsSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSigma
local instance ancientCylinderModelsLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsLocallyPathConnected
local instance ancientCylinderModelsSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModelsSemilocallySimplyConnected

private theorem ancientCylinderModels_local
    (Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M) :
    IsLocalDiffeomorph CylinderI I ∞
      (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
  isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I) (M := F.M))
    Psi.isLocalDiffeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModels_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModels_local target :: scope.openDecls } }

private theorem ancientCylinderModels_metric (T : ℝ)
    (Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b) :
    ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (F.S.family.metric t).inner (UniversalCover.proj (Psi (x, s)))
          (mfderiv CylinderI I (fun p : Cylinder => UniversalCover.proj (Psi p))
            (x, s) (v, a))
          (mfderiv CylinderI I (fun p : Cylinder => UniversalCover.proj (Psi p))
            (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b := by
  intro t ht x s v w a b
  exact (cylinderCover_projection_inner (F.S.family.metric t) Psi
    (x, s) (v, a) (w, b)).trans (hproduct t ht x s v w a b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModels_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderModels_metric target :: scope.openDecls } }

theorem ancientKappa_null_plane_cylinder_topological_models {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (x₀ : F.M) (v₀ w₀ : TangentSpace I x₀)
    (hplane : 0 <
      (F.S.family.metric t₀).inner x₀ v₀ v₀ *
        (F.S.family.metric t₀).inner x₀ w₀ w₀ -
          ((F.S.family.metric t₀).inner x₀ v₀ w₀) ^ 2)
    (hnull : F.S.base.rm04 t₀ x₀ (vec4 (I := I) v₀ w₀ w₀ v₀) = 0) :
    ∃ T : ℝ, 0 < T ∧ ∃ pi : Cylinder → F.M,
      IsLocalDiffeomorph CylinderI I ∞ pi ∧ Function.Surjective pi ∧
      (∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (F.S.family.metric t).inner (pi (x, s))
            (mfderiv CylinderI I pi (x, s) (v, a))
            (mfderiv CylinderI I pi (x, s) (w, b)) =
          (2 * (T - t)) * (sphereMetric).inner x v w + a * b) ∧
      ((∃ d : Cylinder ≃ₘ⟮CylinderI, I⟯ F.M, ∀ p : Cylinder, d p = pi p) ∨
        (∃ d : (SphereAntipodalQuotient × ℝ) ≃ₜ F.M,
          ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) = pi p) ∨
        ∃ d : CylinderDiagonalQuotient ≃ₜ F.M,
          ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) = pi p) := by
  obtain ⟨T, hT, Psi, hproduct, hsurjective, hcases⟩ :=
    ancientKappa_null_plane_fixed_cylinder_deck_fibres F hF hdim
      t₀ ht₀ x₀ v₀ w₀ hplane hnull
  have hlocal := ancientCylinderModels_local F Psi
  rcases hcases with ⟨_, hsingle⟩ | ⟨_, hsphere | ⟨c, hdiagonal⟩⟩
  · have hinjective : Function.Injective
        (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
      fun p q hpq => ((hsingle p q).mp hpq).symm
    obtain ⟨d, hd⟩ := cylinderCover_exists_diffeomorph_of_injective
      Psi hinjective hsurjective
    exact ⟨T, hT, _, hlocal, hsurjective,
      ancientCylinderModels_metric F T Psi hproduct, Or.inl ⟨d, hd⟩⟩
  · have hfibres : ∀ p q : Cylinder,
        UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
          q = p ∨ q = (-p.1, p.2) := by
      simpa only [ancientCylinderModels_antipodal] using hsphere
    obtain ⟨d, hd⟩ := SphereAntipodalQuotient.exists_product_homeomorph
      (fun p : Cylinder => UniversalCover.proj (Psi p))
      hlocal.contMDiff.continuous hlocal.isOpenMap hsurjective hfibres
    exact ⟨T, hT, _, hlocal, hsurjective,
      ancientCylinderModels_metric F T Psi hproduct, Or.inr (Or.inl ⟨d, hd⟩)⟩
  · let Psi' := (cylinderLineTranslation c).trans Psi
    have hlocal' := ancientCylinderModels_local F Psi'
    have hsurjective' := cylinderDeck_recenter_surjective Psi hsurjective c
    have hfibres : ∀ p q : Cylinder,
        UniversalCover.proj (Psi' p) = UniversalCover.proj (Psi' q) ↔
          q = p ∨ q = (-p.1, -p.2) := by
      simpa only [ancientCylinderModels_antipodal] using
        cylinderDeck_recenter_fibres Psi c hdiagonal
    obtain ⟨d, hd⟩ := CylinderDiagonalQuotient.exists_homeomorph
      (fun p : Cylinder => UniversalCover.proj (Psi' p))
      hlocal'.contMDiff.continuous hlocal'.isOpenMap hsurjective' hfibres
    have hproduct' := cylinderLineTranslation_trans_pullback
      F.S.family.metric T Psi hproduct c
    exact ⟨T, hT, _, hlocal', hsurjective',
      ancientCylinderModels_metric F T Psi' hproduct', Or.inr (Or.inr ⟨d, hd⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_topological_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_topological_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_topological_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_topological_models

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
