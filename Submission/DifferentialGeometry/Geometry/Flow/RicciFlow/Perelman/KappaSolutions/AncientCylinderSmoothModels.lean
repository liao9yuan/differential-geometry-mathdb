import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderTopologicalModels
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent

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
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance ancientCylinderSmoothSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothSphereDimension target :: scope.openDecls } }

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientCylinderSmoothTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothTopology
local instance ancientCylinderSmoothCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothCharted
local instance ancientCylinderSmoothManifold : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothManifold
local instance ancientCylinderSmoothT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientCylinderSmoothT2

theorem ancientKappa_null_plane_cylinder_smooth_models {kappa : ℝ}
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
        (∃ d : (SphereAntipodalQuotient × ℝ) ≃ₘ⟮CylinderI, I⟯ F.M,
          ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) = pi p) ∨
        ∃ d : CylinderDiagonalQuotient ≃ₘ⟮CylinderI, I⟯ F.M,
          ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) = pi p) := by
  obtain ⟨T, hT, pi, hlocal, hsurj, hmetric, hcases⟩ :=
    ancientKappa_null_plane_cylinder_topological_models F hF hdim
      t₀ ht₀ x₀ v₀ w₀ hplane hnull
  refine ⟨T, hT, pi, hlocal, hsurj, hmetric, ?_⟩
  rcases hcases with htrivial | ⟨d, hd⟩ | ⟨d, hd⟩
  · exact Or.inl htrivial
  · have hq : IsLocalDiffeomorph CylinderI CylinderI ∞
        SphereAntipodalQuotient.productProjection :=
      isLocalDiffeomorph_prod_real SphereAntipodalQuotient.proj
        SphereAntipodalQuotient.isLocalDiffeomorph_proj
    obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      SphereAntipodalQuotient.productProjection hq
      SphereAntipodalQuotient.surjective_productProjection pi hlocal d hd
    refine Or.inr (Or.inl ⟨D, ?_⟩)
    intro p
    rw [hD]
    exact hd p
  · obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      CylinderDiagonalQuotient.proj CylinderDiagonalQuotient.isLocalDiffeomorph_proj
      CylinderDiagonalQuotient.surjective_proj pi hlocal d hd
    refine Or.inr (Or.inr ⟨D, ?_⟩)
    intro p
    rw [hD]
    exact hd p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_smooth_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_smooth_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_smooth_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_smooth_models

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
