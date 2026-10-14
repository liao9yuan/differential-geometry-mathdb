import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.OpenTarget
import Submission.DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem weaklyMonotoneDiskCompetitors_component_inclusion_iff
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) :
    q ∈ weaklyMonotoneDiskCompetitors
        (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) (loopInComponent γ) ↔
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0), M)).comp q) ∈
          weaklyMonotoneDiskCompetitors g γ := by
  constructor
  · rintro ⟨⟨τ, hτ, ht⟩, L, hL⟩
    refine ⟨⟨τ, hτ, ?_⟩, L, ?_⟩
    · ext θ
      exact congrArg Subtype.val (congrArg (fun w => w θ) ht)
    · intro x y
      simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        Metric.edistOf_restrictOpen_connCompOpen] using hL x y
  · rintro ⟨⟨τ, hτ, ht⟩, L, hL⟩
    refine ⟨⟨τ, hτ, ?_⟩, L, ?_⟩
    · ext θ
      exact congrArg (fun w => w θ) ht
    · intro x y
      rw [Metric.edistOf_restrictOpen_connCompOpen]
      exact hL x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors_component_inclusion_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors_component_inclusion_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors_component_inclusion_iff ``Submission.DifferentialGeometry.Geometry.weaklyMonotoneDiskCompetitors_component_inclusion_iff

theorem disk_energy_values_eq_component
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    ((fun q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)) =>
      riemannianDiskEnergy (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) q) ''
      weaklyMonotoneDiskCompetitors
        (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) (loopInComponent γ)) =
      ((fun q : C(closedDisk, M) => riemannianDiskEnergy g q) ''
        weaklyMonotoneDiskCompetitors g γ) := by
  ext a
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(⟨Subtype.val, continuous_subtype_val⟩ :
      C(connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0), M)).comp q,
      (weaklyMonotoneDiskCompetitors_component_inclusion_iff g γ q).mp hq, ?_⟩
    exact (riemannianDiskEnergy_restrictOpen g _ q).symm
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨τ, _, ht⟩ := hq.1
    let qC := diskInLoopComponent γ τ q ht
    refine ⟨qC, ?_, ?_⟩
    · exact (weaklyMonotoneDiskCompetitors_component_inclusion_iff g γ qC).mpr hq
    · exact riemannianDiskEnergy_restrictOpen g
        (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)) qC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.disk_energy_values_eq_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.disk_energy_values_eq_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.disk_energy_values_eq_component ``Submission.DifferentialGeometry.Geometry.disk_energy_values_eq_component

theorem disk_energy_inf_eq_component
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    sInf ((fun q : C(closedDisk, connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)) =>
      riemannianDiskEnergy (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) q) ''
      weaklyMonotoneDiskCompetitors
        (g.restrictOpen (connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))) (loopInComponent γ)) =
      _root_.InfSet.sInf ((fun q : C(closedDisk, M) => riemannianDiskEnergy g q) ''
        weaklyMonotoneDiskCompetitors g γ) :=
  congrArg _root_.InfSet.sInf (disk_energy_values_eq_component g γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.disk_energy_inf_eq_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.disk_energy_inf_eq_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.disk_energy_inf_eq_component ``Submission.DifferentialGeometry.Geometry.disk_energy_inf_eq_component

end DifferentialGeometry.Geometry
