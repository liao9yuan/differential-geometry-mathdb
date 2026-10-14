import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Mathlib.Topology.Separation.Hausdorff
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedCompactLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactLimitTopology target :: scope.openDecls } }
private local instance pointedCompactLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactLimitCharted target :: scope.openDecls } }
private local instance pointedCompactApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactApproxTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactApproxTopology target :: scope.openDecls } }
private local instance pointedCompactApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactApproxCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactApproxCharted target :: scope.openDecls } }
private local instance pointedCompactApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactApproxT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedCompactApproxT2 target :: scope.openDecls } }

theorem pointedMaps_eventually_compactEmbedding
    {S : Type*} [TopologicalSpace S] [CompactSpace S]
    (e : S → L.M) (he : _root_.Topology.IsEmbedding e) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ f : C(S, (X.obj (subseq k)).M),
        IsClosedEmbedding f ∧ ∀ x : S, f x = Phi.map k (e x) := by
  obtain ⟨k0, hk0⟩ := Phi.source_subset (isCompact_range he.continuous)
  refine ⟨k0, fun k hk => ?_⟩
  have hsource : ∀ x : S, e x ∈ Phi.source k :=
    fun x => hk0 k hk (Set.mem_range_self x)
  have hcontinuous : Continuous (fun x : S => Phi.map k (e x)) := by
    apply continuousOn_univ.mp
    exact (Phi.partialDiffeomorph k).toOpenPartialHomeomorph.continuousOn.comp
      he.continuous.continuousOn (fun x _ => hsource x)
  have hinjective : Function.Injective (fun x : S => Phi.map k (e x)) := by
    intro x y hxy
    exact he.injective ((Phi.partialDiffeomorph k).toPartialEquiv.injOn
      (hsource x) (hsource y) hxy)
  exact ⟨⟨_, hcontinuous⟩, hcontinuous.isClosedEmbedding hinjective, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactEmbedding

open scoped _root_.ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S] [CompactSpace S]

theorem pointedMaps_eventually_compactSmoothEmbedding
    (e : S → L.M) (he : Manifold.IsSmoothEmbedding J I ∞ e) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ f : C(S, (X.obj (subseq k)).M),
        Manifold.IsSmoothEmbedding J I ∞ f ∧
          _root_.Topology.IsClosedEmbedding f ∧ ∀ x : S, f x = Phi.map k (e x) := by
  obtain ⟨k0, hk0⟩ := Phi.source_subset (isCompact_range he.isEmbedding.continuous)
  refine ⟨k0, fun k hk => ?_⟩
  have hsource : Set.range e ⊆ (Phi.partialDiffeomorph k).source := hk0 k hk
  let : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  have hs : Manifold.IsSmoothEmbedding J I ∞ (Phi.map k ∘ e) :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph
      (Phi.partialDiffeomorph k) he hsource
  let f : C(S, (X.obj (subseq k)).M) := ⟨Phi.map k ∘ e, hs.isEmbedding.continuous⟩
  let : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  exact ⟨f, hs, hs.isEmbedding.continuous.isClosedEmbedding hs.isEmbedding.injective,
    fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_eventually_compactSmoothEmbedding


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
