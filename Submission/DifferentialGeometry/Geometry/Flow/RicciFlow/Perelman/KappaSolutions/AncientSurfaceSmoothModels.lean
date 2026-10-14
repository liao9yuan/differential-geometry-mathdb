import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceFixedCover
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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance ancientSurfaceModelsSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsSphereDimension target :: scope.openDecls } }

theorem exists_antipodal_quotient_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (pi : SphereTwo → M) (hlocal : IsLocalDiffeomorph (𝓡 2) I ∞ pi)
    (hsurj : Function.Surjective pi)
    (hfibres : ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x) :
    ∃ d : SphereAntipodalQuotient ≃ₘ⟮𝓡 2, I⟯ M,
      ∀ x : SphereTwo, d (SphereAntipodalQuotient.proj x) = pi x := by
  obtain ⟨d, hd⟩ := SphereAntipodalQuotient.exists_homeomorph pi
    hlocal.isLocalHomeomorph.continuous hlocal.isLocalHomeomorph.isOpenMap hsurj hfibres
  obtain ⟨D, hD⟩ := exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
    SphereAntipodalQuotient.proj SphereAntipodalQuotient.isLocalDiffeomorph_proj
    SphereAntipodalQuotient.surjective_proj pi hlocal d hd
  refine ⟨D, ?_⟩
  intro x
  rw [hD]
  exact hd x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_antipodal_quotient_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_antipodal_quotient_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_antipodal_quotient_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_antipodal_quotient_diffeomorph

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance ancientSurfaceModelsTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsTopology target :: scope.openDecls } }
private local instance ancientSurfaceModelsCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsCharted target :: scope.openDecls } }
private local instance ancientSurfaceModelsSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSurfaceModelsSmooth target :: scope.openDecls } }

theorem ancientKappaSurface_fixed_smooth_models
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ T : ℝ, 0 < T ∧ ∃ pi : SphereTwo → F.M,
      IsLocalDiffeomorph (𝓡 2) I ∞ pi ∧ IsCoveringMap pi ∧ Function.Surjective pi ∧
      (∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        (F.S.family.metric t).inner (pi x)
            (mfderiv (𝓡 2) I pi x v) (mfderiv (𝓡 2) I pi x w) =
          (2 * (T - t)) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w) ∧
      ((∃ d : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M, ∀ x : SphereTwo, d x = pi x) ∨
        ∃ d : SphereAntipodalQuotient ≃ₘ⟮𝓡 2, I⟯ F.M,
          ∀ x : SphereTwo, d (SphereAntipodalQuotient.proj x) = pi x) ∧
      (∀ d : SphereTwo ≃ₜ SphereTwo, pi ∘ d = pi →
        d = Homeomorph.refl SphereTwo ∨ ∀ x : SphereTwo, d x = -x) := by
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
  obtain ⟨hT, pi, hlocal, hcover, hsurj, hmetric, hcases, hdeck⟩ :=
    ancientKappaSurface_fixed_round_cover F hF hdim
  refine ⟨_, hT, pi, hlocal, hcover, hsurj, hmetric, ?_, hdeck⟩
  rcases hcases with hsphere | hfibres
  · exact Or.inl hsphere
  · exact Or.inr (exists_antipodal_quotient_diffeomorph pi hlocal hsurj hfibres)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_smooth_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_smooth_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_smooth_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_smooth_models

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
