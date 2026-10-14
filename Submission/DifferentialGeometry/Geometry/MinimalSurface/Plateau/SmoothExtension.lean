import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskTrace
import Submission.DifferentialGeometry.Geometry.Metric.ConvexSourceLipschitz
import Submission.DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import Submission.DifferentialGeometry.Topology.Manifold.ClosedDiskExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ComplexConjugate _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]



def SmoothDiskExtension (u : C(closedDisk, M)) (U : ℂ → M) : Prop :=
  (∀ z : closedDisk, U z = u z) ∧ ∃ N : Set ℂ, IsOpen N ∧
    Metric.closedBall (0 : ℂ) 1 ⊆ N ∧ ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension



theorem SmoothDiskExtension.smoothUpToBoundary {u : C(closedDisk, M)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E) u U) : DiskSmoothUpToBoundary (E := E) u := by
  obtain ⟨heq, N, _, hDN, hU⟩ := h
  apply (hU.mono hDN).congr
  intro z hz
  exact (diskExtension_coe u ⟨z, hz⟩).trans (heq ⟨z, hz⟩).symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.SmoothDiskExtension
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.smoothUpToBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.smoothUpToBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.smoothUpToBoundary ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.smoothUpToBoundary



theorem SmoothDiskExtension.comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (f : C(M, N)) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    SmoothDiskExtension (E := F) (f.comp u) (f ∘ U) := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  exact ⟨fun z => congrArg f (heq z), s, hs, hDs, hf.comp_contMDiffOn hU⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.comp ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.comp

theorem SmoothDiskExtension.eventuallyEq_diskExtension {u : C(closedDisk, M)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E) u U) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    U =ᶠ[𝓝 z] diskExtension u := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  have hwD : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hw
  rw [diskExtension_coe u ⟨w, hwD⟩]
  exact heq ⟨w, hwD⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.eventuallyEq_diskExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.eventuallyEq_diskExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.eventuallyEq_diskExtension ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.eventuallyEq_diskExtension

theorem SmoothDiskExtension.comp_diskReflection {u : C(closedDisk, M)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E) u U) :
    SmoothDiskExtension (E := E) (u.comp ⟨diskReflection, diskReflection.continuous⟩) (U ∘ conj) := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  refine ⟨fun z => ?_, conj ⁻¹' N, hN.preimage Complex.continuous_conj, fun z hz => ?_, ?_⟩
  · have hc : conj (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using z.property
    have hz' : (⟨conj (z : ℂ), hc⟩ : closedDisk) = diskReflection z := Subtype.ext rfl
    have huse := heq ⟨conj (z : ℂ), hc⟩
    rw [hz'] at huse
    change U (conj (z : ℂ)) = u (diskReflection z)
    exact huse
  · exact hDN (by simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz)
  · exact hU.comp ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contMDiff.contMDiffOn) (fun z hz => hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.comp_diskReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.comp_diskReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.comp_diskReflection ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.comp_diskReflection

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_smoothDiskExtension_of_locally_extendable
    (u : C(closedDisk, M))
    (hloc : ∀ x : closedDisk, ∃ U : ℂ → M, ∃ V : Set ℂ,
      IsOpen V ∧ (x : ℂ) ∈ V ∧ ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U V ∧
        ∀ y : closedDisk, (y : ℂ) ∈ V → U y = u y) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U := by
  obtain ⟨U, _, heq, N, hN, hKN, hUs⟩ :=
    DifferentialGeometry.Topology.exists_contMDiffOn_extension_closedBall
      (I := 𝓘(ℝ, E)) (n := ⊤) (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) u hloc
  exact ⟨U, heq, N, hN, hKN, hUs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_locally_extendable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_locally_extendable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_locally_extendable ``Submission.DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_locally_extendable




theorem exists_smoothDiskExtension_of_diskSmoothUpToBoundary [CompleteSpace E]
    {u : C(closedDisk, M)} (hu : DiskSmoothUpToBoundary (E := E) u) :
    ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U := by
  obtain ⟨g, _, heq, N, hN, hKN, hgs⟩ :=
    DifferentialGeometry.Topology.exists_contMDiffOn_extension_closedDisk
      (I := 𝓘(ℝ, E)) (show ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
        (diskExtension u) (Metric.closedBall (0 : ℂ) 1) from hu)
  exact ⟨g, fun z => (heq z.property).trans (diskExtension_coe u z), N, hN, hKN, hgs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_diskSmoothUpToBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_diskSmoothUpToBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_diskSmoothUpToBoundary ``Submission.DifferentialGeometry.Geometry.exists_smoothDiskExtension_of_diskSmoothUpToBoundary

theorem diskSmoothUpToBoundary_iff_exists_smoothDiskExtension [CompleteSpace E]
    (u : C(closedDisk, M)) :
    DiskSmoothUpToBoundary (E := E) u ↔ ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U :=
  ⟨exists_smoothDiskExtension_of_diskSmoothUpToBoundary,
    fun ⟨_, hU⟩ => hU.smoothUpToBoundary⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskSmoothUpToBoundary_iff_exists_smoothDiskExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskSmoothUpToBoundary_iff_exists_smoothDiskExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskSmoothUpToBoundary_iff_exists_smoothDiskExtension ``Submission.DifferentialGeometry.Geometry.diskSmoothUpToBoundary_iff_exists_smoothDiskExtension

theorem SmoothDiskExtension.lipschitz (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {U : ℂ → M} (h : SmoothDiskExtension (E := E) u U) :
    ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  have hU1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U N := hU.of_le (by simp)
  obtain ⟨L, hL⟩ := exists_compact_source_mfderiv_bound g hN hU1
    (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1) hDN
  refine ⟨L, fun z w => ?_⟩
  rw [← heq z, ← heq w]
  exact riemannian_edist_le_on_convex_source g hN hU1 hDN
    (convex_closedBall (0 : ℂ) 1) hL z.property w.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.lipschitz ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.lipschitz

end DifferentialGeometry.Geometry
