import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedDomainLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainLimitTopology target :: scope.openDecls } }
private local instance pointedDomainLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainLimitCharted target :: scope.openDecls } }
private local instance pointedDomainLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainLimitSmooth target :: scope.openDecls } }

private local instance pointedDomainApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainApproxTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainApproxTopology target :: scope.openDecls } }
private local instance pointedDomainApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainApproxCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainApproxCharted target :: scope.openDecls } }
private local instance pointedDomainApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainApproxSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainApproxSmooth target :: scope.openDecls } }

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S] [IsManifold J ∞ S]

theorem pointedMaps_restrict_isSmoothEmbedding
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) :
    IsSmoothEmbedding J I ∞ (fun x : U => Phi.map k (e x)) := by
  have hlocal : IsLocalDiffeomorphOn J I ∞ (Phi.map k ∘ e) U := by
    intro x
    exact (e.isLocalDiffeomorph (x : S)).comp (K := I) (X.obj (subseq k)).M
      ((Phi.partialDiffeomorph k).isLocalDiffeomorphAt I I ∞ (hU ⟨x, x.2, rfl⟩))
  have hrestricted : IsLocalDiffeomorph J I ∞ (fun x : U => Phi.map k (e x)) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open U hlocal
  apply localDiffeomorph_isSmoothEmbedding_of_injective hrestricted
  intro x y hxy
  apply Subtype.ext
  apply e.injective
  exact (Phi.partialDiffeomorph k).toPartialEquiv.injOn
    (hU ⟨x, x.2, rfl⟩) (hU ⟨y, y.2, rfl⟩) hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_restrict_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_restrict_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_restrict_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_restrict_isSmoothEmbedding

def pointedDomainEmbedding
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) : C(U, (X.obj (subseq k)).M) where
  toFun x := Phi.map k (e x)
  continuous_toFun :=
    (pointedMaps_restrict_isSmoothEmbedding Phi e U k hU).isEmbedding.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding

@[simp] theorem pointedDomainEmbedding_apply
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S) (k : ℕ)
    (hU : e '' (U : Set S) ⊆ Phi.source k) (x : U) :
    pointedDomainEmbedding Phi e U k hU x = Phi.map k (e x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedDomainEmbedding_apply

theorem pointedMaps_eventually_fixedDomainEmbedding
    (e : S ≃ₘ⟮J, I⟯ L.M) (U : TopologicalSpace.Opens S)
    (K : Set S) (hK : IsCompact K) (hUK : (U : Set S) ⊆ K) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ f : C(U, (X.obj (subseq k)).M),
        IsSmoothEmbedding J I ∞ f ∧ ∀ x : U, f x = Phi.map k (e x) := by
  obtain ⟨k0, hk0⟩ := Phi.source_subset (hK.image e.continuous)
  refine ⟨k0, fun k hk => ?_⟩
  have hU : e '' (U : Set S) ⊆ Phi.source k :=
    (_root_.Set.image_mono hUK).trans (hk0 k hk)
  exact ⟨pointedDomainEmbedding Phi e U k hU,
    pointedMaps_restrict_isSmoothEmbedding Phi e U k hU, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomainEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomainEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomainEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_fixedDomainEmbedding

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
