import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetExtension
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetDifferential
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import Submission.DifferentialGeometry.Topology.LoopSpace.ManifoldComponent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.Filter _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem isSmoothEmbeddedLoop_open_inclusion_iff (N : TopologicalSpace.Opens M)
    (γ : freeLoop N) :
    IsSmoothEmbeddedLoop (E := E)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(N, M)).comp γ) ↔
      IsSmoothEmbeddedLoop (E := E) γ := by
  have hs := contMDiff_subtypeVal_comp_iff (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, E))
    (n := ∞) N (fun t : ℝ => γ (t : loopCircle))
  have he := Topology.IsEmbedding.of_comp_iff (f := γ)
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : N → M))
  have hd (t : ℝ) := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, E)) N (fun s : ℝ => γ (s : loopCircle)) t
  constructor
  · intro h
    refine ⟨hs.mp h.smooth, he.mp h.embedding, fun t => ?_⟩
    have ht := h.immersed t
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (Subtype.val ∘ (fun s : ℝ => γ (s : loopCircle))) t 1 ≠ 0 at ht
    rw [hd t] at ht
    exact ht
  · intro h
    refine ⟨hs.mpr h.smooth, he.mpr h.embedding, fun t => ?_⟩
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (Subtype.val ∘ (fun s : ℝ => γ (s : loopCircle))) t 1 ≠ 0
    rw [hd t]
    exact h.immersed t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isSmoothEmbeddedLoop_open_inclusion_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isSmoothEmbeddedLoop_open_inclusion_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isSmoothEmbeddedLoop_open_inclusion_iff ``Submission.DifferentialGeometry.Geometry.isSmoothEmbeddedLoop_open_inclusion_iff



theorem SmoothDiskExtension.exists_open_corestriction_differential
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (N : TopologicalSpace.Opens M) [T2Space N]
    {u : C(closedDisk, N)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(N, M)).comp u) U) :
    ∃ V : ℂ → N, SmoothDiskExtension (E := E) u V ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Subtype.val ∘ V) =ᶠ[𝓝 z] U) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        DiskMapConformalAt (g.restrictOpen N) V z ↔ DiskMapConformalAt g U z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        (diskMapTension (g.restrictOpen N) V z : E) = diskMapTension g U z := by
  obtain ⟨V, hV, heq⟩ := h.exists_open_corestriction N
  refine ⟨V, hV, heq, ?_, ?_⟩
  · intro z hz
    exact (diskMapConformalAt_restrictOpen g N V z).trans
      (diskMapConformalAt_congr_of_eventuallyEq g (heq z hz))
  · intro z hz
    obtain ⟨S, hS, hDS, hs⟩ := hV.2
    have hc := ((hs z (hDS hz)).contMDiffAt (hS.mem_nhds (hDS hz))).continuousAt
    exact (diskMapTension_restrictOpen g N V z hc).trans
      (diskMapTension_congr_of_eventuallyEq g (heq z hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction_differential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction_differential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction_differential ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_open_corestriction_differential

variable [T2Space M]




theorem IsConformalMinimizingDisk.corestrict_component
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (h : IsConformalMinimizingDisk g γ u σ U) :
    ∃ V : ℂ → loopComponentOpen E γ,
      IsConformalMinimizingDisk (g.restrictOpen (loopComponentOpen E γ))
        (loopInComponent γ) (diskInLoopComponent γ σ u h.trace) σ V ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Subtype.val ∘ V) =ᶠ[𝓝 z] U := by
  let N := loopComponentOpen E γ
  let uN : C(closedDisk, N) := diskInLoopComponent γ σ u h.trace
  let ι : C(N, M) := ⟨Subtype.val, continuous_subtype_val⟩
  have hιu : ι.comp uN = u := by ext z; rfl
  have hext : SmoothDiskExtension (E := E) (ι.comp uN) U := hιu.symm ▸ h.extension
  obtain ⟨V, hV, heq, hconf, htension⟩ := hext.exists_open_corestriction_differential g N
  refine ⟨V, ⟨hV, h.positiveTrace, diskInLoopComponent_trace γ σ u h.trace,
    fun z hz => (hconf z hz).mpr (h.conformal z hz), ?_, ?_⟩, heq⟩
  · intro z hz
    exact (htension z hz).trans (h.harmonic z hz)
  · intro v hv ht
    have hvM := (diskSmoothUpToBoundary_open_inclusion_iff N v).mpr hv
    have htM : diskTrace (ι.comp v) = γ := by
      ext θ
      exact congrArg Subtype.val (congrArg (fun f => f θ) ht)
    have hmin := h.minimizesSmooth (ι.comp v) hvM htM
    rw [riemannianDiskArea_restrictOpen, riemannianDiskArea_restrictOpen]
    exact hmin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.corestrict_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsConformalMinimizingDisk.corestrict_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.corestrict_component ``Submission.DifferentialGeometry.Geometry.IsConformalMinimizingDisk.corestrict_component




theorem IsConformalMinimizingDisk.component_inclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    {u : C(closedDisk, loopComponentOpen E γ)} {σ : C(loopCircle, loopCircle)}
    {U : ℂ → loopComponentOpen E γ}
    (h : IsConformalMinimizingDisk (g.restrictOpen (loopComponentOpen E γ))
      (loopInComponent γ) u σ U) :
    IsConformalMinimizingDisk g γ
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(loopComponentOpen E γ, M)).comp u)
      σ (Subtype.val ∘ U) := by
  let N := loopComponentOpen E γ
  let ι : C(N, M) := ⟨Subtype.val, continuous_subtype_val⟩
  refine ⟨h.extension.comp ι (contMDiff_subtype_val (I := 𝓘(ℝ, E))), h.positiveTrace,
    ?_, ?_, ?_, ?_⟩
  · ext θ
    exact congrArg Subtype.val (congrArg (fun f => f θ) h.trace)
  · intro z hz
    exact (diskMapConformalAt_restrictOpen g N U z).mp (h.conformal z hz)
  · intro z hz
    obtain ⟨S, hS, hDS, hU⟩ := h.extension.2
    have hc := ((hU z (hDS hz)).contMDiffAt (hS.mem_nhds (hDS hz))).continuousAt
    exact (diskMapTension_restrictOpen g N U z hc).symm.trans (h.harmonic z hz)
  · intro v hv ht
    have ht' : diskTrace v = γ.comp (ContinuousMap.id loopCircle) := by simpa using ht
    let vN : C(closedDisk, N) := diskInLoopComponent γ (ContinuousMap.id loopCircle) v ht'
    have hvN : DiskSmoothUpToBoundary (E := E) vN :=
      (diskSmoothUpToBoundary_open_inclusion_iff N vN).mp hv
    have htN : diskTrace vN = loopInComponent γ := by
      exact (diskInLoopComponent_trace γ (ContinuousMap.id loopCircle) v ht').trans
        (ContinuousMap.comp_id _)
    have hmin := h.minimizesSmooth vN hvN htN
    rw [riemannianDiskArea_restrictOpen, riemannianDiskArea_restrictOpen] at hmin
    exact hmin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.component_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsConformalMinimizingDisk.component_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsConformalMinimizingDisk.component_inclusion ``Submission.DifferentialGeometry.Geometry.IsConformalMinimizingDisk.component_inclusion

end DifferentialGeometry.Geometry
