import Submission.DifferentialGeometry.Topology.Manifold.SphereDirection
import Submission.DifferentialGeometry.Topology.ClosedBall.ClosedAnnulus
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianWithinSign
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

section Coordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereCylinderInclusion (q : _root_.Metric.sphere (0 : E) 1 × unitInterval) : E :=
  (1 + q.2.1) • (q.1 : E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion ``Submission.DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion

def sphereCylinderProjection (v : _root_.Metric.sphere (0 : E) 1) (x : E) :
    sphere (0 : E) 1 × unitInterval :=
  (sphereDirection v x, _root_.Set.projIcc 0 1 zero_le_one (‖x‖ - 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereCylinderProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereCylinderProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereCylinderProjection ``Submission.DifferentialGeometry.Topology.Manifold.sphereCylinderProjection

theorem norm_sphereCylinderInclusion (q : _root_.Metric.sphere (0 : E) 1 × unitInterval) :
    ‖sphereCylinderInclusion q‖ = 1 + q.2.1 := by
  have hpos : 0 < 1 + q.2.1 := by linarith [q.2.2.1]
  simp [sphereCylinderInclusion, norm_smul, norm_eq_of_mem_sphere, abs_of_pos hpos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.norm_sphereCylinderInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.norm_sphereCylinderInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.norm_sphereCylinderInclusion ``Submission.DifferentialGeometry.Topology.Manifold.norm_sphereCylinderInclusion

theorem sphereCylinderProjection_inclusion (v : _root_.Metric.sphere (0 : E) 1)
    (q : _root_.Metric.sphere (0 : E) 1 × unitInterval) :
    sphereCylinderProjection v (sphereCylinderInclusion q) = q := by
  apply Prod.ext
  · exact sphereDirection_pos_smul v q.1 (by linarith [q.2.2.1])
  · change _root_.Set.projIcc 0 1 zero_le_one (‖sphereCylinderInclusion q‖ - 1) = q.2
    rw [norm_sphereCylinderInclusion, add_sub_cancel_left, _root_.Set.projIcc_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereCylinderProjection_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereCylinderProjection_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereCylinderProjection_inclusion ``Submission.DifferentialGeometry.Topology.Manifold.sphereCylinderProjection_inclusion

theorem sphereCylinderInclusion_projection (v : _root_.Metric.sphere (0 : E) 1)
    {x : E} (hx : ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2) :
    sphereCylinderInclusion (sphereCylinderProjection v x) = x := by
  have hband : ‖x‖ - 1 ∈ _root_.Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hnx : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
  change (1 + (_root_.Set.projIcc 0 1 zero_le_one (‖x‖ - 1)).1) • (sphereDirection v x : E) = x
  rw [_root_.Set.projIcc_of_mem _ hband]
  dsimp only
  rw [add_sub_cancel]
  exact norm_smul_sphereDirection v hnx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion_projection ``Submission.DifferentialGeometry.Topology.Manifold.sphereCylinderInclusion_projection

end Coordinates

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

theorem contMDiff_sphereCylinderInclusion :
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ (sphereCylinderInclusion (E := E)) :=
  (contMDiff_const.add (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiff_sphereCylinderInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiff_sphereCylinderInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiff_sphereCylinderInclusion ``Submission.DifferentialGeometry.Topology.Manifold.contMDiff_sphereCylinderInclusion

theorem contMDiffOn_sphereCylinderProjection (v : _root_.Metric.sphere (0 : E) 1) :
    ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod (𝓡∂ 1)) ∞ (sphereCylinderProjection v)
      {x : E | ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2} := by
  have hne (x : E) (hx : ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2) : x ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
  have hd : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (sphereDirection v)
      {x : E | ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2} :=
    (contMDiffOn_sphereDirection v).mono (fun x hx ↦ hne x hx)
  have ht : ContDiffOn ℝ ∞ (fun x : E ↦ ‖x‖ - 1)
      {x : E | ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2} := fun x hx ↦
    ((contDiffAt_norm ℝ (hne x hx)).sub contDiffAt_const).contDiffWithinAt
  exact hd.prodMk (contMDiffOn_projIcc.comp ht.contMDiffOn
    (fun x hx ↦ by constructor <;> linarith [hx.1, hx.2]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereCylinderProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereCylinderProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereCylinderProjection ``Submission.DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereCylinderProjection

def sphereCylinderAnnulusEquiv (v : _root_.Metric.sphere (0 : E) 1)
    (Ψ : Diffeomorph ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1))
      (_root_.Metric.sphere (0 : E) 1 × unitInterval) (_root_.Metric.sphere (0 : E) 1 × unitInterval) ∞) :
    PartialEquiv E E where
  toFun := fun x ↦ sphereCylinderInclusion (Ψ (sphereCylinderProjection v x))
  invFun := fun x ↦ sphereCylinderInclusion (Ψ.symm (sphereCylinderProjection v x))
  source := {x | ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2}
  target := {x | ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2}
  map_source' := by
    intro x _
    change ‖sphereCylinderInclusion (Ψ (sphereCylinderProjection v x))‖ ∈ _root_.Set.Icc (1 : ℝ) 2
    rw [norm_sphereCylinderInclusion]
    have ht := (Ψ (sphereCylinderProjection v x)).2.2
    constructor <;> linarith [ht.1, ht.2]
  map_target' := by
    intro x _
    change ‖sphereCylinderInclusion (Ψ.symm (sphereCylinderProjection v x))‖ ∈ _root_.Set.Icc (1 : ℝ) 2
    rw [norm_sphereCylinderInclusion]
    have ht := (Ψ.symm (sphereCylinderProjection v x)).2.2
    constructor <;> linarith [ht.1, ht.2]
  left_inv' := by
    intro x hx
    rw [sphereCylinderProjection_inclusion, Ψ.symm_apply_apply]
    exact sphereCylinderInclusion_projection v hx
  right_inv' := by
    intro x hx
    rw [sphereCylinderProjection_inclusion, Ψ.apply_symm_apply]
    exact sphereCylinderInclusion_projection v hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereCylinderAnnulusEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereCylinderAnnulusEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereCylinderAnnulusEquiv ``Submission.DifferentialGeometry.Topology.Manifold.sphereCylinderAnnulusEquiv

theorem contDiffOn_sphereCylinderAnnulusEquiv (v : _root_.Metric.sphere (0 : E) 1)
    (Ψ : Diffeomorph ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1))
      (_root_.Metric.sphere (0 : E) 1 × unitInterval) (_root_.Metric.sphere (0 : E) 1 × unitInterval) ∞) :
    ContDiffOn ℝ ∞ (sphereCylinderAnnulusEquiv v Ψ) (sphereCylinderAnnulusEquiv v Ψ).source ∧
      ContDiffOn ℝ ∞ (sphereCylinderAnnulusEquiv v Ψ).symm (sphereCylinderAnnulusEquiv v Ψ).target := by
  constructor
  · exact ((contMDiff_sphereCylinderInclusion.comp Ψ.contMDiff).comp_contMDiffOn
      (contMDiffOn_sphereCylinderProjection v)).contDiffOn
  · exact ((contMDiff_sphereCylinderInclusion.comp Ψ.symm.contMDiff).comp_contMDiffOn
      (contMDiffOn_sphereCylinderProjection v)).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contDiffOn_sphereCylinderAnnulusEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contDiffOn_sphereCylinderAnnulusEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contDiffOn_sphereCylinderAnnulusEquiv ``Submission.DifferentialGeometry.Topology.Manifold.contDiffOn_sphereCylinderAnnulusEquiv

theorem det_sphereCylinderAnnulusEquiv_pos_iff (hrank : 1 < Module.rank ℝ E)
    (v : _root_.Metric.sphere (0 : E) 1)
    (Ψ : Diffeomorph ((𝓡 n).prod (𝓡∂ 1)) ((𝓡 n).prod (𝓡∂ 1))
      (_root_.Metric.sphere (0 : E) 1 × unitInterval) (_root_.Metric.sphere (0 : E) 1 × unitInterval) ∞)
    {x y : E} (hx : ‖x‖ ∈ _root_.Set.Icc (1 : ℝ) 2) (hy : ‖y‖ ∈ _root_.Set.Icc (1 : ℝ) 2) :
    0 < (fderivWithin ℝ (sphereCylinderAnnulusEquiv v Ψ)
      {z | ‖z‖ ∈ _root_.Set.Icc (1 : ℝ) 2} x).toLinearMap.det ↔
    0 < (fderivWithin ℝ (sphereCylinderAnnulusEquiv v Ψ)
      {z | ‖z‖ ∈ _root_.Set.Icc (1 : ℝ) 2} y).toLinearMap.det := by
  let c := sphereCylinderAnnulusEquiv v Ψ
  obtain ⟨hf, hg⟩ := contDiffOn_sphereCylinderAnnulusEquiv v Ψ
  exact DifferentialGeometry.Analysis.det_fderivWithin_pos_iff_of_inverse
    (DifferentialGeometry.Analysis.uniqueDiffOn_norm_band zero_lt_one (by norm_num))
    (DifferentialGeometry.Analysis.isConnected_norm_band hrank zero_lt_one (by norm_num)).isPreconnected
    c c.symm hf hg c.mapsTo (fun _ hz ↦ c.left_inv hz) hx hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.det_sphereCylinderAnnulusEquiv_pos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.det_sphereCylinderAnnulusEquiv_pos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.det_sphereCylinderAnnulusEquiv_pos_iff ``Submission.DifferentialGeometry.Topology.Manifold.det_sphereCylinderAnnulusEquiv_pos_iff

end Smooth
end DifferentialGeometry.Topology.Manifold
