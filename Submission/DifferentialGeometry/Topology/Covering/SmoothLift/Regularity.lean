import Submission.DifferentialGeometry.Topology.Covering.SmoothLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Topology _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

theorem exists_contMDiff_lift_of_simplyConnected
    {E F G H H' H'' W M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    [TopologicalSpace W] [ChartedSpace H W] [SimplyConnectedSpace W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H'' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {L : ModelWithCorners ℝ G H''} {n : ℕ∞ω}
    {p : N → M} (hp : IsCoveringMap p) (hps : IsLocalDiffeomorph L J n p)
    (f : W → M) (hf : ContMDiff I J n f) (w₀ : W) (n₀ : N) (hn₀ : p n₀ = f w₀) :
    ∃ g : C(W, N), g w₀ = n₀ ∧ (∀ x, p (g x) = f x) ∧ ContMDiff I L n g := by
  have : LocallyPathConnectedSpace W :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  obtain ⟨g, ⟨hg₀, hpg⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    ⟨f, hf.continuous⟩ w₀ n₀ hn₀
  have hpg' : ∀ x, p (g x) = f x := fun x => congrFun hpg x
  refine ⟨g, hg₀, hpg', ?_⟩
  intro x
  obtain ⟨φ, hx, hφ⟩ := hps (g x)
  have hfx : f x ∈ φ.target := by
    rw [← hpg' x, hφ hx]
    exact φ.map_source hx
  have hs := (φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hfx)).comp x (hf x)
  apply hs.congr_of_eventuallyEq
  filter_upwards [g.continuous.continuousAt.preimage_mem_nhds
    (φ.open_source.mem_nhds hx)] with y hy
  change g y = φ.symm (f y)
  rw [← hpg' y, hφ hy]
  exact (φ.left_inv hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiff_lift_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiff_lift_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiff_lift_of_simplyConnected ``Submission.DifferentialGeometry.Topology.exists_contMDiff_lift_of_simplyConnected

end DifferentialGeometry.Topology
