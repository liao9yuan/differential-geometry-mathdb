import Submission.DifferentialGeometry.Topology.Covering.ImmersionLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology

theorem exists_continuousMap_factor_of_range_subset
    {W M S : Type*} [TopologicalSpace W] [TopologicalSpace M] [TopologicalSpace S]
    {ι : W → M} (hι : _root_.Topology.IsEmbedding ι) (e : C(S, M)) (hsub : _root_.Set.range e ⊆ _root_.Set.range ι) :
    ∃ η : C(S, W), ∀ x, ι (η x) = e x := by
  have hmem (x : S) : ∃ w, ι w = e x := hsub (_root_.Set.mem_range_self x)
  choose η hη using hmem
  have heq : ι ∘ η = e := funext hη
  exact ⟨⟨η, hι.continuous_iff.mpr (heq ▸ e.continuous)⟩, hη⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_continuousMap_factor_of_range_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_continuousMap_factor_of_range_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_continuousMap_factor_of_range_subset ``Submission.DifferentialGeometry.Topology.exists_continuousMap_factor_of_range_subset

theorem exists_embedded_smooth_lift_of_simplyConnected
    {E F H H' W M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace W] [ChartedSpace H W] [SimplyConnectedSpace W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {p : N → M} (hp : IsCoveringMap p) (hps : IsLocalDiffeomorph J J ∞ p)
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : _root_.Topology.IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (w₀ : W) (n₀ : N) (hn₀ : p n₀ = ι w₀) :
    ∃ g : C(W, N), g w₀ = n₀ ∧ (∀ w, p (g w) = ι w) ∧
      ContMDiff I J ∞ g ∧ _root_.Topology.IsEmbedding g ∧
      ∀ w, Function.Injective (mfderiv I J g w) := by
  obtain ⟨g, hg₀, hpg, hgs⟩ := exists_smooth_lift_of_simplyConnected hp hps ι hι w₀ n₀ hn₀
  have heq : p ∘ g = ι := funext hpg
  exact ⟨g, hg₀, hpg, hgs,
    IsEmbedding.of_comp g.continuous hps.contMDiff.continuous (heq ▸ hemb),
    injective_mfderiv_of_smooth_lift hps.contMDiff hinj hgs hpg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_embedded_smooth_lift_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_embedded_smooth_lift_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_embedded_smooth_lift_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_embedded_smooth_lift_of_simplyConnected

end DifferentialGeometry.Topology
