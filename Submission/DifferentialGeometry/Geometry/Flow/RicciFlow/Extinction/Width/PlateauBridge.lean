import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauClassical
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskTensionSmoothness
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Topology _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section StandardModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
def smoothDisk_of_smoothDiskExtension {u : C(Disk, Q)} {U : ℂ → Q}
    (h : Geometry.SmoothDiskExtension (E := E) u U) :
    SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q) where
  map := u
  smooth z := by
    obtain ⟨heq, N, hN, hDN, hUN⟩ := h
    refine ⟨{
      map := U
      domain := N
      isOpen_domain := hN
      mem_domain := hDN z.property
      smooth := hUN
      agrees := ?_ }⟩
    intro w hw
    rw [heq ⟨w, hw.2⟩]
    exact (diskExtension_coe u ⟨w, hw.2⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smoothDisk_of_smoothDiskExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smoothDisk_of_smoothDiskExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smoothDisk_of_smoothDiskExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smoothDisk_of_smoothDiskExtension

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem SmoothDisk.differential_eq_diskMapPartial (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    {U : ℂ → Q} (h : Geometry.SmoothDiskExtension (E := E) w.map U) (z : Disk) (v : ℂ) :
    (w.differential z v : E) = (Geometry.diskMapPartial U z v : E) := by
  obtain ⟨heq, N, hN, hDN, hUN⟩ := h
  have hcongr : _root_.Set.EqOn (diskExtension (⇑w.map)) U (Metric.closedBall (0 : ℂ) 1) := by
    intro y hy
    rw [diskExtension_coe w.map ⟨y, hy⟩, heq ⟨y, hy⟩]
  have h1 : mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (⇑w.map))
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) =
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (Metric.closedBall (0 : ℂ) 1) (z : ℂ) :=
    mfderivWithin_congr_of_mem hcongr z.property
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z : ℂ) :=
    (hUN.contMDiffAt (hN.mem_nhds (hDN z.property))).mdifferentiableAt (by simp)
  have h2 : mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (Metric.closedBall (0 : ℂ) 1) (z : ℂ) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z : ℂ) :=
    hmd.hasMFDerivAt.hasMFDerivWithinAt.mfderivWithin
      (disk_uniqueDiffWithinAt z).uniqueMDiffWithinAt
  change mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (⇑w.map))
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) v = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z : ℂ) v
  exact congrArg (fun (L : ℂ →L[ℝ] E) => (L v : E)) (h1.trans h2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.differential_eq_diskMapPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.differential_eq_diskMapPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.differential_eq_diskMapPartial ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.differential_eq_diskMapPartial

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem SmoothDisk.diskSmoothUpToBoundary (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) :
    Geometry.DiskSmoothUpToBoundary (E := E) w.map :=
  w.contMDiffOn_extension.congr fun z hz =>
    (Geometry.diskExtension_coe w.map ⟨z, hz⟩).trans
      (diskExtension_coe w.map ⟨z, hz⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskSmoothUpToBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskSmoothUpToBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskSmoothUpToBoundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskSmoothUpToBoundary

theorem SmoothDisk.isConformalAt_iff_diskMapConformalAt
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (h : Geometry.SmoothDiskExtension (E := E) w.map U) (z : Disk) :
    (g.inner (w.map z) (w.differential z 1) (w.differential z Complex.I) = 0 ∧
      g.inner (w.map z) (w.differential z 1) (w.differential z 1) =
        g.inner (w.map z) (w.differential z Complex.I) (w.differential z Complex.I)) ↔
      Geometry.DiskMapConformalAt g U (z : ℂ) := by
  have hd (v : ℂ) := SmoothDisk.differential_eq_diskMapPartial w h z v
  have hpt : U (z : ℂ) = w.map z := h.1 z
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · rw [hpt, ← hd 1, ← hd Complex.I]
      exact hw.1
    · rw [hpt, ← hd 1, ← hd Complex.I]
      exact hw.2
  · intro hw
    refine ⟨?_, ?_⟩
    · rw [← hpt, hd 1, hd Complex.I]
      exact hw.1
    · rw [← hpt, hd 1, hd Complex.I]
      exact hw.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformalAt_iff_diskMapConformalAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformalAt_iff_diskMapConformalAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformalAt_iff_diskMapConformalAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformalAt_iff_diskMapConformalAt

theorem SmoothDisk.isConformal_iff_diskMapConformalAt
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (h : Geometry.SmoothDiskExtension (E := E) w.map U) :
    w.IsConformal g ↔ ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Geometry.DiskMapConformalAt g U z := by
  constructor
  · intro hw z hz
    exact (SmoothDisk.isConformalAt_iff_diskMapConformalAt w g h ⟨z, hz⟩).mp (hw ⟨z, hz⟩)
  · intro hw z
    exact (SmoothDisk.isConformalAt_iff_diskMapConformalAt w g h z).mpr (hw z z.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_iff_diskMapConformalAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_iff_diskMapConformalAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_iff_diskMapConformalAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_iff_diskMapConformalAt

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
def DiskLocalExtension.of_smoothDiskExtension {u : C(Disk, Q)} {U : ℂ → Q}
    (h : Geometry.SmoothDiskExtension (E := E) u U) (z : Disk) :
    DiskLocalExtension (I := 𝓘(ℝ, E)) u z :=
  let N := Classical.choose h.2
  let hN := Classical.choose_spec h.2
  { map := U
    domain := N
    isOpen_domain := hN.1
    mem_domain := hN.2.1 z.property
    smooth := hN.2.2
    agrees := fun w hw => by
      rw [h.1 ⟨w, hw.2⟩]
      exact (diskExtension_coe u ⟨w, hw.2⟩).symm }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
@[simp] theorem DiskLocalExtension.of_smoothDiskExtension_map
    {u : C(Disk, Q)} {U : ℂ → Q} (h : Geometry.SmoothDiskExtension (E := E) u U) (z : Disk) :
    (DiskLocalExtension.of_smoothDiskExtension h z).map = U := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.DiskLocalExtension.of_smoothDiskExtension_map

variable [FiniteDimensional ℝ E]

theorem diskLocalTension_eq_diskMapTension (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (U : ℂ → Q) (z : ℂ) :
    (diskLocalTension g U z : E) = (Geometry.diskMapTension g U z : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskLocalTension_eq_diskMapTension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskLocalTension_eq_diskMapTension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskLocalTension_eq_diskMapTension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskLocalTension_eq_diskMapTension

theorem SmoothDisk.diskMapTension_eq_zero_of_isHarmonic
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (h : Geometry.SmoothDiskExtension (E := E) w.map U)
    (z : Disk) (hw : w.IsHarmonic g) :
    (Geometry.diskMapTension g U (z : ℂ) : E) = 0 := by
  have h0 := hw z (DiskLocalExtension.of_smoothDiskExtension h z)
  rwa [DiskLocalExtension.of_smoothDiskExtension_map,
    diskLocalTension_eq_diskMapTension] at h0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic

theorem SmoothDisk.diskMapTension_eq_zero_of_isHarmonic_interior
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hw : w.IsHarmonic g) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (Geometry.diskMapTension g (diskExtension (⇑w.map)) z : E) = 0 := by
  have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
  let F := Classical.choice (w.smooth ⟨z, hz'⟩)
  have h0 : diskLocalTension g F.map z = 0 := hw ⟨z, hz'⟩ F
  have hmem : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hgerm : F.map =ᶠ[𝓝 z] diskExtension (⇑w.map) := by
    filter_upwards [F.isOpen_domain.mem_nhds F.mem_domain, hmem] with y hyd hyb
    exact F.agrees ⟨hyd, hyb⟩
  rw [← diskLocalTension_eq_diskMapTension, ← diskLocalTension_congr_germ g F.map _ z hgerm]
  exact h0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic_interior ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.diskMapTension_eq_zero_of_isHarmonic_interior

theorem SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_interior
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      (Geometry.diskMapTension g (diskExtension (⇑w.map)) z : E) = 0) (z : Disk) (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
    ∀ F : DiskLocalExtension (I := 𝓘(ℝ, E)) w.map z, diskLocalTension g F.map (z : ℂ) = 0 := by
  intro F
  have hmem : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 (z : ℂ) :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hgerm : F.map =ᶠ[𝓝 (z : ℂ)] diskExtension (⇑w.map) := by
    filter_upwards [F.isOpen_domain.mem_nhds F.mem_domain, hmem] with y hyd hyb
    exact F.agrees ⟨hyd, hyb⟩
  rw [diskLocalTension_congr_germ g F.map (diskExtension (⇑w.map)) (z : ℂ) hgerm,
    diskLocalTension_eq_diskMapTension]
  exact h z hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_interior ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_interior

omit [FiniteDimensional ℝ E] in
theorem SmoothDisk.isConformal_of_diskMapConformalAt_on_ball
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (h : Geometry.SmoothDiskExtension (E := E) w.map U)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, Geometry.DiskMapConformalAt g U z) :
    w.IsConformal g := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  exact (SmoothDisk.isConformal_iff_diskMapConformalAt w g ⟨heq, N, hN, hDN, hU⟩).mpr
    (Geometry.diskMapConformalAt_of_ball g hN hU hDN hball)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_of_diskMapConformalAt_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_of_diskMapConformalAt_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_of_diskMapConformalAt_on_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isConformal_of_diskMapConformalAt_on_ball

theorem SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_on_ball
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (h : Geometry.SmoothDiskExtension (E := E) w.map U)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, (Geometry.diskMapTension g U z : E) = 0) :
    w.IsHarmonic g := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := h
  intro z F
  have hgermU (w' : ℂ) (hw' : w' ∈ Metric.ball (0 : ℂ) 1) :
      U =ᶠ[𝓝 w'] diskExtension (⇑w.map) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw'] with y hy
    have hyb : y ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hy
    rw [diskExtension_coe w.map ⟨y, hyb⟩]
    exact heq ⟨y, hyb⟩
  have hgermF (w' : ℂ) (hw' : w' ∈ Metric.ball (0 : ℂ) 1)
      (hwd : w' ∈ F.domain) : F.map =ᶠ[𝓝 w'] diskExtension (⇑w.map) := by
    filter_upwards [F.isOpen_domain.mem_nhds hwd,
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hw') Metric.ball_subset_closedBall]
      with y hyd hyb
    exact F.agrees ⟨hyd, hyb⟩
  have hcase : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 ∨ (z : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
    by_cases hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1
    · exact Or.inl hz
    · refine Or.inr ?_
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      exact z.property
  rcases hcase with hz | hz
  · have h1 : (Geometry.diskMapTension g F.map (z : ℂ) : E)
        = (Geometry.diskMapTension g U (z : ℂ) : E) :=
      (Geometry.diskMapTension_congr_of_eventuallyEq g (hgermF _ hz F.mem_domain)).trans
        (Geometry.diskMapTension_congr_of_eventuallyEq g (hgermU _ hz)).symm
    rw [diskLocalTension_eq_diskMapTension]
    exact h1.trans (hball _ hz)
  · have hzero : (Geometry.diskMapTension g F.map (z : ℂ) : E) = 0 :=
      Geometry.diskMapTension_eq_zero_of_mem_closure_ball g F.isOpen_domain F.smooth
        F.mem_domain hz (fun w' hw' hwd => by
          have h1 : (Geometry.diskMapTension g F.map w' : E)
              = (Geometry.diskMapTension g U w' : E) :=
            (Geometry.diskMapTension_congr_of_eventuallyEq g (hgermF _ hw' hwd)).trans
              (Geometry.diskMapTension_congr_of_eventuallyEq g (hgermU _ hw')).symm
          exact h1.trans (hball _ hw'))
    rw [diskLocalTension_eq_diskMapTension]
    exact hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_on_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_on_ball

end StandardModel

section Trace

variable {Q : Type*} [TopologicalSpace Q]

theorem periodic_circle_coe_of_add_one {ψ : ℝ → ℝ}
    (hinc : ∀ t, ψ (t + 1) = ψ t + 1) :
    Function.Periodic (fun t : ℝ => (ψ t : Surgery.Topology.Circle)) 1 := by
  intro t
  change ((ψ (t + 1) : ℝ) : Surgery.Topology.Circle) =
    ((ψ t : ℝ) : Surgery.Topology.Circle)
  rw [hinc t, AddCircle.coe_add, AddCircle.coe_period, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_add_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_add_one

theorem periodic_circle_coe_of_sub_one {ψ : ℝ → ℝ}
    (hinc : ∀ t, ψ (t + 1) = ψ t - 1) :
    Function.Periodic (fun t : ℝ => (ψ t : Surgery.Topology.Circle)) 1 := by
  intro t
  change ((ψ (t + 1) : ℝ) : Surgery.Topology.Circle) =
    ((ψ t : ℝ) : Surgery.Topology.Circle)
  rw [hinc t, sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, AddCircle.coe_period,
    neg_zero, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_sub_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_sub_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_sub_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.periodic_circle_coe_of_sub_one

theorem circleMapOfLift {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hper : Function.Periodic (fun t : ℝ => (ψ t : Surgery.Topology.Circle)) 1) :
    ∃ σ : C(Surgery.Topology.Circle, Surgery.Topology.Circle),
      ∀ t : ℝ, σ (t : Surgery.Topology.Circle) = (ψ t : Surgery.Topology.Circle) :=
  ⟨{ toFun := hper.lift, continuous_toFun := by
      apply isQuotientMap_quotient_mk'.continuous_iff.mpr
      change Continuous (fun x : ℝ => hper.lift (x : Surgery.Topology.Circle))
      have hc : Continuous (fun x : ℝ => (ψ x : Surgery.Topology.Circle)) :=
        (AddCircle.continuous_mk' (1 : ℝ)).comp hψ
      simpa only [Function.Periodic.lift_coe] using hc }, fun t =>
    Function.Periodic.lift_coe hper t⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.circleMapOfLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.circleMapOfLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.circleMapOfLift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.circleMapOfLift

theorem isSignedWeaklyMonotoneTrace_iff_diskWeakJordanTrace (u : C(Disk, Q))
    (γ : ContinuousFreeLoop Q) :
    IsSignedWeaklyMonotoneTrace u γ ↔ Geometry.DiskWeakJordanTrace γ u := by
  constructor
  · rintro ⟨φ, hφ, hm, ht⟩
    have hper : Function.Periodic (fun t : ℝ => (φ t : Surgery.Topology.Circle)) 1 :=
      hm.elim (fun h => periodic_circle_coe_of_add_one h.2)
        (fun h => periodic_circle_coe_of_sub_one h.2)
    obtain ⟨σ, hσ⟩ := circleMapOfLift hφ hper
    refine ⟨σ, ⟨φ, hφ, fun t => (hσ t).symm, hm⟩, ?_⟩
    refine ContinuousMap.ext fun θ => ?_
    refine QuotientAddGroup.induction_on θ ?_
    intro t
    simp only [Topology.diskTrace, ContinuousMap.comp_apply,
      diskBoundary_eq_topologicalDiskBoundary]
    exact (ht t).trans (congrArg γ (hσ t)).symm
  · rintro ⟨σ, ⟨φ, hφ, hσ, hm⟩, htrace⟩
    refine ⟨φ, hφ, hm, fun t => ?_⟩
    have h1 : u (diskBoundary (t : Surgery.Topology.Circle)) = γ (σ (t : Surgery.Topology.Circle)) := by
      have h2 := congrArg (fun f : C(Topology.loopCircle, Q) => f (t : Topology.loopCircle)) htrace
      simpa only [Topology.diskTrace, ContinuousMap.comp_apply,
        diskBoundary_eq_topologicalDiskBoundary] using h2
    exact h1.trans (congrArg γ (hσ t)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSignedWeaklyMonotoneTrace_iff_diskWeakJordanTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSignedWeaklyMonotoneTrace_iff_diskWeakJordanTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSignedWeaklyMonotoneTrace_iff_diskWeakJordanTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSignedWeaklyMonotoneTrace_iff_diskWeakJordanTrace

end Trace

section Loops

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem isSmoothEmbeddedLoop_iff (γ : ContinuousFreeLoop Q) :
    Geometry.IsSmoothEmbeddedLoop (E := E) γ ↔
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ) ∧ Topology.IsEmbedding γ ∧
        ∀ t : ℝ, loopVelocity (I := 𝓘(ℝ, E)) γ t ≠ 0 :=
  ⟨fun h => ⟨h.smooth, h.embedding, h.immersed⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_iff

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem isSmoothEmbeddedLoop_of_regularLoop (γ : RegularLoop 𝓘(ℝ, E) Q)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := 𝓘(ℝ, E)) γ.toContinuousLoop t ≠ 0) :
    Geometry.IsSmoothEmbeddedLoop (E := E) γ.toContinuousLoop :=
  (isSmoothEmbeddedLoop_iff γ.toContinuousLoop).mpr ⟨hsmooth, hemb, himm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_of_regularLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_of_regularLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_of_regularLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.isSmoothEmbeddedLoop_of_regularLoop

end Loops

section Competitors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] in
theorem mem_spanningDiskCompetitors_of_diskCompetitor
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : ContinuousFreeLoop Q)
    (v : DiskCompetitor g γ) : v.1.map ∈ Geometry.spanningDiskCompetitors g γ :=
  (mem_spanningDiskCompetitors_iff g γ v.1.map).mpr ⟨v.2, v.1.isLipschitz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mem_spanningDiskCompetitors_of_diskCompetitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mem_spanningDiskCompetitors_of_diskCompetitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mem_spanningDiskCompetitors_of_diskCompetitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.mem_spanningDiskCompetitors_of_diskCompetitor

omit [FiniteDimensional ℝ E] in
theorem diskArea_eq_riemannianDiskArea_of_diskCompetitor
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : ContinuousFreeLoop Q)
    (v : DiskCompetitor g γ) :
    diskArea g v.1.map = Geometry.riemannianDiskArea g v.1.map :=
  diskArea_eq_riemannianDiskArea g v.1.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_riemannianDiskArea_of_diskCompetitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_riemannianDiskArea_of_diskCompetitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_riemannianDiskArea_of_diskCompetitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_eq_riemannianDiskArea_of_diskCompetitor

section StandardDensity

variable [CompactSpace Q] [T3Space Q]

theorem smooth_exact_disk_density_stdModel
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : RegularLoop 𝓘(ℝ, E) Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (v : DiskCompetitor g γ.toContinuousLoop) :
    ∃ w : ℕ → SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q),
      (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
      Filter.Tendsto (fun j => diskArea g (w j).map) Filter.atTop (𝓝 (diskArea g v.1.map)) := by
  have hv : v.1.map ∈ Geometry.spanningDiskCompetitors g γ.toContinuousLoop :=
    mem_spanningDiskCompetitors_of_diskCompetitor g γ.toContinuousLoop v
  obtain ⟨vj, Uj, hdata, htend⟩ :=
    Geometry.exists_smooth_spanning_disks_smooth_extension_tendsto_area g hγ hv
  refine ⟨fun j => smoothDisk_of_smoothDiskExtension (E := E) (hdata j).1, ?_, ?_⟩
  · intro j θ
    have h1 : (smoothDisk_of_smoothDiskExtension (E := E) (hdata j).1).map = vj j := rfl
    rw [h1]
    exact (diskTrace_eq_iff (vj j) γ.toContinuousLoop).mp (hdata j).2 θ
  · have hfun : (fun j => diskArea g
        (smoothDisk_of_smoothDiskExtension (E := E) (hdata j).1).map) =
        fun j => Geometry.riemannianDiskArea g (vj j) := by
      funext j
      rw [diskArea_eq_riemannianDiskArea]
      rfl
    rw [hfun, diskArea_eq_riemannianDiskArea g v.1.map]
    exact htend

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smooth_exact_disk_density_stdModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smooth_exact_disk_density_stdModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smooth_exact_disk_density_stdModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.smooth_exact_disk_density_stdModel

end StandardDensity

end Competitors

section Transport

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

def SmoothDisk.comp_diffeomorph (Φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂)
    (u : SmoothDisk (I := I₁) (Q := M₁)) : SmoothDisk (I := I₂) (Q := M₂) where
  map := ⟨fun z => Φ (u.map z), Φ.continuous.comp u.map.continuous⟩
  smooth z := by
    obtain ⟨F⟩ := u.smooth z
    refine ⟨{
      map := fun w => Φ (F.map w)
      domain := F.domain
      isOpen_domain := F.isOpen_domain
      mem_domain := F.mem_domain
      smooth := Φ.contMDiff.comp_contMDiffOn F.smooth
      agrees := ?_ }⟩
    intro w hw
    simp only [diskExtension, dif_pos hw.2, F.agrees ⟨hw.1, hw.2⟩, ContinuousMap.coe_mk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph

def InteriorSmoothDisk.comp_diffeomorph (Φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂)
    (u : InteriorSmoothDisk (I := I₁) (Q := M₁)) : InteriorSmoothDisk (I := I₂) (Q := M₂) where
  map := ⟨fun z => Φ (u.map z), Φ.continuous.comp u.map.continuous⟩
  smooth z hz := by
    obtain ⟨F⟩ := u.smooth z hz
    refine ⟨{
      map := fun w => Φ (F.map w)
      domain := F.domain
      isOpen_domain := F.isOpen_domain
      mem_domain := F.mem_domain
      smooth := Φ.contMDiff.comp_contMDiffOn F.smooth
      agrees := ?_ }⟩
    intro w hw
    simp only [diskExtension, dif_pos hw.2, F.agrees ⟨hw.1, hw.2⟩, ContinuousMap.coe_mk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.InteriorSmoothDisk.comp_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.InteriorSmoothDisk.comp_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.InteriorSmoothDisk.comp_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.InteriorSmoothDisk.comp_diffeomorph

omit [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] in
theorem IsSignedWeaklyMonotoneTrace.comp_diffeomorph (Φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂)
    {u : Disk → M₁} {γ : ContinuousFreeLoop M₁} (h : IsSignedWeaklyMonotoneTrace u γ) :
    IsSignedWeaklyMonotoneTrace (fun z => Φ (u z))
      ((⟨Φ, Φ.continuous⟩ : C(M₁, M₂)).comp γ) := by
  obtain ⟨φ, hφ, hm, ht⟩ := h
  exact ⟨φ, hφ, hm, fun t => congrArg Φ (ht t)⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsSignedWeaklyMonotoneTrace
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsSignedWeaklyMonotoneTrace.comp_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsSignedWeaklyMonotoneTrace.comp_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsSignedWeaklyMonotoneTrace.comp_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.IsSignedWeaklyMonotoneTrace.comp_diffeomorph

omit [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] in
theorem SmoothDisk.comp_diffeomorph_map (Φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂)
    (u : SmoothDisk (I := I₁) (Q := M₁)) (z : Disk) :
    (SmoothDisk.comp_diffeomorph Φ u).map z = Φ (u.map z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.SmoothDisk.comp_diffeomorph_map

variable [FiniteDimensional ℝ E₁] [T2Space M₁]

theorem riemannianAreaDensity_pullbackMetricCross
    (g : SmoothRiemannianMetric I₂ M₂) (Ψ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (U : ℂ → M₁) (z : ℂ) :
    Geometry.riemannianAreaDensity (Diffeomorph.pullbackMetricCross g Ψ) U z =
      Geometry.riemannianAreaDensity g (fun w => Ψ (U w)) z := by
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) I₁ U z
  · have hd : mfderiv 𝓘(ℝ, ℂ) I₂ (fun w => Ψ (U w)) z =
        (mfderiv I₁ I₂ (Ψ : M₁ → M₂) (U z)).comp (mfderiv 𝓘(ℝ, ℂ) I₁ U z) :=
      mfderiv_comp z (Ψ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) hU
    have hv (c : ℂ) : (mfderiv I₁ I₂ (Ψ : M₁ → M₂) (U z))
        ((mfderiv 𝓘(ℝ, ℂ) I₁ U z) c) =
        (mfderiv 𝓘(ℝ, ℂ) I₂ (fun w => Ψ (U w)) z) c := by
      rw [hd]
      rfl
    simp only [Geometry.riemannianAreaDensity, Geometry.tangentTwoJacobian,
      Diffeomorph.pullbackMetricCross_inner, hv]
  · have hU' : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I₂ (fun w => Ψ (U w)) z := by
      intro h
      refine hU ?_
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) I₁ (fun w => Ψ.symm (Ψ (U w))) z :=
        (Ψ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)).comp z h
      have heq : (fun w => Ψ.symm (Ψ (U w))) = U :=
        funext fun w => Ψ.symm_apply_apply (U w)
      rwa [heq] at hcomp
    rw [Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt _ hU']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianAreaDensity_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianAreaDensity_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianAreaDensity_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianAreaDensity_pullbackMetricCross

theorem riemannianDiskArea_pullbackMetricCross
    (g : SmoothRiemannianMetric I₂ M₂) (Ψ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (u : Disk → M₁) :
    Geometry.riemannianDiskArea (Diffeomorph.pullbackMetricCross g Ψ) u =
      Geometry.riemannianDiskArea g (fun z => Ψ (u z)) := by
  rw [Geometry.riemannianDiskArea, Geometry.riemannianDiskArea]
  refine _root_.MeasureTheory.integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  rw [riemannianAreaDensity_pullbackMetricCross]
  refine Geometry.riemannianAreaDensity_congr g ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  simp only [Geometry.diskExtension, Function.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.riemannianDiskArea_pullbackMetricCross

theorem diskArea_pullbackMetricCross
    (g : SmoothRiemannianMetric I₂ M₂) (Ψ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂) (u : Disk → M₁) :
    diskArea (Diffeomorph.pullbackMetricCross g Ψ) u = diskArea g (fun z => Ψ (u z)) := by
  rw [diskArea_eq_riemannianDiskArea, diskArea_eq_riemannianDiskArea,
    riemannianDiskArea_pullbackMetricCross]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_pullbackMetricCross

theorem diskArea_comp_diffeomorph (Φ : M₁ ≃ₘ⟮I₁, I₂⟯ M₂)
    (g : SmoothRiemannianMetric I₂ M₂) (u : SmoothDisk (I := I₁) (Q := M₁)) :
    diskArea (Diffeomorph.pullbackMetricCross g Φ) u.map =
      diskArea g (fun z => Φ (u.map z)) :=
  diskArea_pullbackMetricCross g Φ u.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_comp_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_comp_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_comp_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.diskArea_comp_diffeomorph

end Transport

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
