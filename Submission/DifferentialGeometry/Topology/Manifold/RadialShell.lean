import Submission.DifferentialGeometry.Topology.Manifold.SphereCylinderAnnulus
import Mathlib.Geometry.Manifold.Algebra.Structures

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E]

section Basic
variable [NormedSpace ℝ E]

def radialShell (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ) (v : _root_.Metric.sphere (0 : E) 1) : Set E :=
  {x | x ≠ p ∧ ‖x - p‖ ∈ _root_.Set.Icc (a (sphereDirection v (x - p))) (b (sphereDirection v (x - p)))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialShell ``Submission.DifferentialGeometry.Topology.Manifold.radialShell

def radialShellInclusion (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (q : _root_.Metric.sphere (0 : E) 1 × unitInterval) : E :=
  (a q.1 + (b q.1 - a q.1) * q.2.1) • (q.1 : E) + p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialShellInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialShellInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialShellInclusion ``Submission.DifferentialGeometry.Topology.Manifold.radialShellInclusion

def radialShellProjection (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (v : _root_.Metric.sphere (0 : E) 1) (x : E) : _root_.Metric.sphere (0 : E) 1 × unitInterval :=
  let u := sphereDirection v (x - p)
  (u, _root_.Set.projIcc 0 1 zero_le_one ((‖x - p‖ - a u) / (b u - a u)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialShellProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialShellProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialShellProjection ``Submission.DifferentialGeometry.Topology.Manifold.radialShellProjection

private theorem radial_interpolation_mem (a b : ℝ) (hab : a < b) (t : unitInterval) :
    a + (b - a) * t.1 ∈ _root_.Set.Icc a b := by
  constructor
  · nlinarith [t.2.1]
  · nlinarith [t.2.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.radial_interpolation_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.radial_interpolation_mem target :: scope.openDecls } }

private theorem normalized_radius_mem {a b t : ℝ} (hab : a < b) (ht : t ∈ _root_.Set.Icc a b) :
    (t - a) / (b - a) ∈ _root_.Set.Icc (0 : ℝ) 1 := by
  rw [_root_.Set.mem_Icc, le_div_iff₀ (sub_pos.mpr hab), _root_.MulZeroClass.zero_mul, div_le_one (sub_pos.mpr hab)]
  constructor <;> linarith [ht.1, ht.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.normalized_radius_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.normalized_radius_mem target :: scope.openDecls } }

theorem norm_radialShellInclusion_sub (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (ha : ∀ u, 0 < a u) (hab : ∀ u, a u < b u) (q : _root_.Metric.sphere (0 : E) 1 × unitInterval) :
    ‖radialShellInclusion p a b q - p‖ = a q.1 + (b q.1 - a q.1) * q.2.1 := by
  have hpos := lt_of_lt_of_le (ha q.1) (radial_interpolation_mem _ _ (hab q.1) q.2).1
  simp only [radialShellInclusion, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hpos, norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.norm_radialShellInclusion_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.norm_radialShellInclusion_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.norm_radialShellInclusion_sub ``Submission.DifferentialGeometry.Topology.Manifold.norm_radialShellInclusion_sub

theorem radialShellProjection_inclusion (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (v : _root_.Metric.sphere (0 : E) 1) (ha : ∀ u, 0 < a u) (hab : ∀ u, a u < b u)
    (q : _root_.Metric.sphere (0 : E) 1 × unitInterval) :
    radialShellProjection p a b v (radialShellInclusion p a b q) = q := by
  have hpos := lt_of_lt_of_le (ha q.1) (radial_interpolation_mem _ _ (hab q.1) q.2).1
  have hdir : sphereDirection v (radialShellInclusion p a b q - p) = q.1 := by
    simp only [radialShellInclusion, add_sub_cancel_right]
    exact sphereDirection_pos_smul v q.1 hpos
  apply Prod.ext
  · exact hdir
  · change _root_.Set.projIcc 0 1 zero_le_one
      ((‖radialShellInclusion p a b q - p‖ - a (sphereDirection v (radialShellInclusion p a b q - p))) /
        (b (sphereDirection v (radialShellInclusion p a b q - p)) -
          a (sphereDirection v (radialShellInclusion p a b q - p)))) = q.2
    rw [hdir, norm_radialShellInclusion_sub p a b ha hab]
    have heq : (a q.1 + (b q.1 - a q.1) * q.2.1 - a q.1) / (b q.1 - a q.1) = q.2.1 := by
      field_simp [(sub_pos.mpr (hab q.1)).ne']
      ring
    rw [heq, _root_.Set.projIcc_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialShellProjection_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialShellProjection_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialShellProjection_inclusion ``Submission.DifferentialGeometry.Topology.Manifold.radialShellProjection_inclusion

theorem radialShellInclusion_projection (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (v : _root_.Metric.sphere (0 : E) 1) (hab : ∀ u, a u < b u)
    {x : E} (hx : x ∈ radialShell p a b v) :
    radialShellInclusion p a b (radialShellProjection p a b v x) = x := by
  let u := sphereDirection v (x - p)
  have ht := normalized_radius_mem (hab u) hx.2
  change (a u + (b u - a u) * (_root_.Set.projIcc 0 1 zero_le_one ((‖x - p‖ - a u) / (b u - a u))).1) •
      (u : E) + p = x
  rw [_root_.Set.projIcc_of_mem _ ht]
  dsimp only
  have heq : a u + (b u - a u) * ((‖x - p‖ - a u) / (b u - a u)) = ‖x - p‖ := by
    field_simp [(sub_pos.mpr (hab u)).ne']
    ring
  rw [heq, norm_smul_sphereDirection v (sub_ne_zero.mpr hx.1), sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialShellInclusion_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialShellInclusion_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialShellInclusion_projection ``Submission.DifferentialGeometry.Topology.Manifold.radialShellInclusion_projection

def radialShellEquiv (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ) (v : _root_.Metric.sphere (0 : E) 1)
    (ha : ∀ u, 0 < a u) (hab : ∀ u, a u < b u) :
    PartialEquiv (_root_.Metric.sphere (0 : E) 1 × unitInterval) E where
  toFun := radialShellInclusion p a b
  invFun := radialShellProjection p a b v
  source := _root_.Set.univ
  target := radialShell p a b v
  map_source' := by
    intro q _
    have hnorm := norm_radialShellInclusion_sub p a b ha hab q
    have hrange := radial_interpolation_mem _ _ (hab q.1) q.2
    have hpos := lt_of_lt_of_le (ha q.1) hrange.1
    have hdir : sphereDirection v (radialShellInclusion p a b q - p) = q.1 := by
      simp only [radialShellInclusion, add_sub_cancel_right]
      exact sphereDirection_pos_smul v q.1 hpos
    refine ⟨?_, ?_⟩
    · intro heq
      rw [heq, sub_self, norm_zero] at hnorm
      exact hpos.ne' hnorm.symm
    · rw [hdir, hnorm]
      exact hrange
  map_target' := fun _ _ ↦ _root_.Set.mem_univ _
  left_inv' := fun q _ ↦ radialShellProjection_inclusion p a b v ha hab q
  right_inv' := fun _ hx ↦ radialShellInclusion_projection p a b v hab hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialShellEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialShellEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialShellEquiv ``Submission.DifferentialGeometry.Topology.Manifold.radialShellEquiv

end Basic
section Smooth
variable [InnerProductSpace ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]

theorem contMDiff_radialShellInclusion (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ a) (hb : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ b) :
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ (radialShellInclusion p a b) :=
  (((ha.comp contMDiff_fst).add (((hb.comp contMDiff_fst).sub (ha.comp contMDiff_fst)).mul
      (contMDiff_subtypeVal_Icc.comp contMDiff_snd))).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)).add contMDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiff_radialShellInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiff_radialShellInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiff_radialShellInclusion ``Submission.DifferentialGeometry.Topology.Manifold.contMDiff_radialShellInclusion

theorem contMDiffOn_radialShellProjection (p : E) (a b : _root_.Metric.sphere (0 : E) 1 → ℝ)
    (v : _root_.Metric.sphere (0 : E) 1) (hab : ∀ u, a u < b u)
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ a) (hb : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ b) :
    ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod (𝓡∂ 1)) ∞ (radialShellProjection p a b v)
      (radialShell p a b v) := by
  have hd : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (fun x ↦ sphereDirection v (x - p))
      (radialShell p a b v) :=
    (contMDiffOn_sphereDirection v).comp (contDiff_id.sub contDiff_const).contMDiff.contMDiffOn
      (fun _ hx ↦ sub_ne_zero.mpr hx.1)
  have hn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun x ↦ ‖x - p‖) (radialShell p a b v) := by
    intro x hx
    exact ((contDiffAt_norm ℝ (sub_ne_zero.mpr hx.1)).comp x
      (contDiffAt_id.sub contDiffAt_const)).contMDiffAt.contMDiffWithinAt
  have hden := (hb.comp_contMDiffOn hd).sub (ha.comp_contMDiffOn hd)
  have hdenne : ∀ x ∈ radialShell p a b v,
      b (sphereDirection v (x - p)) - a (sphereDirection v (x - p)) ≠ 0 :=
    fun _ _ ↦ ne_of_gt (sub_pos.mpr (hab _))
  have ht : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun x ↦ (‖x - p‖ - a (sphereDirection v (x - p))) /
        (b (sphereDirection v (x - p)) - a (sphereDirection v (x - p))))
      (radialShell p a b v) := by
    have hm := (hn.sub (ha.comp_contMDiffOn hd)).mul (hden.inv₀ hdenne)
    apply hm.congr
    intro x _
    exact (div_eq_mul_inv _ _).symm
  exact hd.prodMk (contMDiffOn_projIcc.comp ht
    (fun _ hx ↦ normalized_radius_mem (hab _) hx.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiffOn_radialShellProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiffOn_radialShellProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiffOn_radialShellProjection ``Submission.DifferentialGeometry.Topology.Manifold.contMDiffOn_radialShellProjection

end Smooth
end DifferentialGeometry.Topology.Manifold
