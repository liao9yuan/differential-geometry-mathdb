import Submission.DifferentialGeometry.Topology.Manifold.Small
import Submission.DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Submission.DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import Mathlib.Topology.Instances.Shrink

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

universe w

namespace DifferentialGeometry.Manifold

theorem exists_small_diffeomorph
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
    [ChartedSpace H M] [IsManifold I ∞ M] [LindelofSpace M]
    (L : E ≃L[𝕜] F) :
    ∃ (N : Type w) (_ : TopologicalSpace N) (hcs : ChartedSpace F N),
      let _ := hcs
      ∃ hman : IsManifold 𝓘(𝕜, F) ∞ N,
        let _ := hman
        Nonempty (N ≃ₘ⟮𝓘(𝕜, F), I⟯ M) := by
  let e : H ≃ₜ F := I.toHomeomorph.trans L.toHomeomorph
  let _ : Small.{w} H := small_of_injective e.injective
  let _ : Small.{w} M := ChartedSpace.small_of_lindelofSpace H M
  have hc : ∀ y : H, 𝓘(𝕜, F) (e y) = L (I y) := fun _ => rfl
  let C : ChartedSpace F M := chartedSpaceTransHomeomorph (M := M) e
  let hM : let _ := C; IsManifold 𝓘(𝕜, F) ∞ M :=
    isManifold_transHomeomorph (M := M) I 𝓘(𝕜, F) e L hc
  let Φ : let _ := C; M ≃ₘ⟮𝓘(𝕜, F), I⟯ M := by
    let _ := C
    let _ := hM
    refine ⟨Equiv.refl M, ?_, ?_⟩
    · change ContMDiff 𝓘(𝕜, F) I ∞ (id : M → M)
      exact (contMDiff_chartedSpaceTransHomeomorph_iff I 𝓘(𝕜, F) e L hc
        (I₀ := 𝓘(𝕜, F)) (f := id)).mp contMDiff_id
    · change ContMDiff I 𝓘(𝕜, F) ∞ (id : M → M)
      exact (contMDiff_chartedSpaceTransHomeomorph_iff I 𝓘(𝕜, F) e L hc
        (I₀ := I) (f := id)).mpr contMDiff_id
  let _ := C
  let _ := hM
  let eN : Shrink.{w} M ≃ₜ M := (Shrink.homeomorph M).symm
  let CN := Homeomorph.pullbackChartedSpace (H := F) eN
  let _ := CN
  let hN := Homeomorph.instIsManifoldPullback (I := 𝓘(𝕜, F)) (n := ∞) eN
  let _ := hN
  exact ⟨Shrink.{w} M, inferInstance, CN, hN,
    ⟨(Homeomorph.pullbackDiffeomorph (I := 𝓘(𝕜, F)) (n := ∞) eN).trans Φ⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.exists_small_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.exists_small_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.exists_small_diffeomorph ``Submission.DifferentialGeometry.Manifold.exists_small_diffeomorph

end DifferentialGeometry.Manifold
