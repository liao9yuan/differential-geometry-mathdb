import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace Manifold
open _root_.Manifold

open _root_.Manifold _root_.Manifold.IsImmersion in
theorem IsImmersion.isImmersionOfComplement_of_finrank_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E V C : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [FiniteDimensional 𝕜 C]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞} {f : M → N}
    (h : _root_.Manifold.IsImmersion I J n f)
    (hdim : Module.finrank 𝕜 C = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    IsImmersionOfComplement C I J n f := by
  intro x
  let hi := h.isImmersionOfComplement_complement x
  let : FiniteDimensional 𝕜 (E × h.complement) :=
    FiniteDimensional.of_injective hi.equiv.toLinearEquiv.toLinearMap hi.equiv.injective
  let : FiniteDimensional 𝕜 E :=
    FiniteDimensional.of_injective (LinearMap.inl 𝕜 E h.complement)
      LinearMap.inl_injective
  let : FiniteDimensional 𝕜 h.complement :=
    FiniteDimensional.of_injective (LinearMap.inr 𝕜 E h.complement)
      LinearMap.inr_injective
  have hsum : Module.finrank 𝕜 E + Module.finrank 𝕜 h.complement = Module.finrank 𝕜 V := by
    simpa only [Module.finrank_prod] using hi.equiv.toLinearEquiv.finrank_eq
  have hrank : Module.finrank 𝕜 h.complement = Module.finrank 𝕜 C := by omega
  exact hi.trans_F (ContinuousLinearEquiv.ofFinrankEq hrank)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersion.isImmersionOfComplement_of_finrank_eq then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersion.isImmersionOfComplement_of_finrank_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersion.isImmersionOfComplement_of_finrank_eq ``Submission.Manifold.IsImmersion.isImmersionOfComplement_of_finrank_eq

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.not_surjective_of_finrank_ne
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
    [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞} {f : M → N}
    (hf : _root_.Manifold.IsSmoothEmbedding I J n f) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 E ≠ Module.finrank 𝕜 F) :
    ¬ Function.Surjective f := by
  intro hs
  obtain ⟨x⟩ := ‹Nonempty M›
  let A := ((hf.diffeomorphOfSurjective hs).isLocalDiffeomorph x).mfderivToContinuousLinearEquiv hn
  exact hdim A.toLinearEquiv.finrank_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.not_surjective_of_finrank_ne then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.not_surjective_of_finrank_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.not_surjective_of_finrank_ne ``Submission.Manifold.IsSmoothEmbedding.not_surjective_of_finrank_ne

end Manifold
