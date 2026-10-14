import Submission.DifferentialGeometry.Topology.Ehresmann.ProductHeight
import Submission.DifferentialGeometry.Topology.Manifold.IntervalReflection
import Submission.DifferentialGeometry.Topology.Connected.TwoComponentPartition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

theorem exists_intervalProduct_with_labeled_ends
    {E F H G W B M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace W] [ChartedSpace H W]
    [TopologicalSpace B] [ChartedSpace G B] [CompactSpace B] [Nonempty B]
    [TopologicalSpace M] [T2Space M]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [BoundarylessManifold J B]
    (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞)
    (ι : W → M) (hι : Continuous ι) (hinj : Function.Injective ι)
    (S₀ S₁ : Set M) (hS₀ : IsPreconnected S₀) (hS₁ : IsPreconnected S₁)
    (hbdy : ι '' I.boundary W = S₀ ∪ S₁) :
    ∃ D' : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞,
      _root_.Set.range (fun p : B ↦ ι (D' (p, 0))) = S₀ ∧
      range (fun p : B ↦ ι (D' (p, 1))) = S₁ := by
  let A₀ := _root_.Set.range (fun p : B ↦ ι (D (p, 0)))
  let A₁ := _root_.Set.range (fun p : B ↦ ι (D (p, 1)))
  have hc (t : unitInterval) : Continuous (fun p : B ↦ ι (D (p, t))) :=
    hι.comp (D.continuous.comp (continuous_id.prodMk continuous_const))
  have hclosed₀ : IsClosed A₀ := (isCompact_range (hc 0)).isClosed
  have hclosed₁ : IsClosed A₁ := (isCompact_range (hc 1)).isClosed
  have hnonempty₀ : A₀.Nonempty := _root_.Set.range_nonempty _
  have hnonempty₁ : A₁.Nonempty := _root_.Set.range_nonempty _
  have hd : Disjoint A₀ A₁ := by
    apply disjoint_left.mpr
    rintro _ ⟨p, hp⟩ ⟨q, hq⟩
    have h := congrArg Prod.snd (D.injective (hinj (hp.trans hq.symm)))
    exact zero_ne_one h
  have hcover : S₀ ∪ S₁ = A₀ ∪ A₁ := by
    rw [← hbdy, boundary_eq_range_intervalProduct_ends D, _root_.Set.image_union,
      ← _root_.Set.range_comp, ← _root_.Set.range_comp]
    rfl
  rcases DifferentialGeometry.Topology.eq_or_eq_of_two_preconnected_closed_partitions
    hS₀ hS₁ hnonempty₀ hnonempty₁ hclosed₀ hclosed₁ hd hcover with h | h
  · exact ⟨D, h.1.symm, h.2.symm⟩
  · let R := (Diffeomorph.refl J B ∞).prodCongr DifferentialGeometry.Topology.Manifold.unitIntervalReflection
    refine ⟨R.trans D, ?_, ?_⟩
    · change _root_.Set.range (fun p : B ↦ ι (D (p, unitInterval.symm 0))) = S₀
      simpa only [unitInterval.symm_zero] using h.1.symm
    · change _root_.Set.range (fun p : B ↦ ι (D (p, unitInterval.symm 1))) = S₁
      simpa only [unitInterval.symm_one] using h.2.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.exists_intervalProduct_with_labeled_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.exists_intervalProduct_with_labeled_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.exists_intervalProduct_with_labeled_ends ``Submission.DifferentialGeometry.Topology.Ehresmann.exists_intervalProduct_with_labeled_ends

end DifferentialGeometry.Topology.Ehresmann
