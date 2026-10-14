import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.LocalDiffeomorphStraightening
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_stereographic_cylinder_reparametrization :
    ∃ D : ℝ ≃ₘ[ℝ] ℝ, StrictMono D ∧ D '' _root_.Set.Icc (0 : ℝ) 1 = _root_.Set.Icc (0 : ℝ) 1 ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 0] (fun t => t / 15) ∧
      (D : ℝ → ℝ) =ᶠ[𝓝 1] (fun t => (16 / (2 - t) - 1) / 15) := by
  have h₀ : ContDiffOn ℝ ∞ (fun t : ℝ => t / 15) univ := by fun_prop
  have h₁ : ContDiffOn ℝ ∞ (fun t : ℝ => (16 / (2 - t) - 1) / 15) (_root_.Set.Iio 2) := by
    exact ((contDiffOn_const.div (contDiffOn_const.sub contDiffOn_id)
      (fun t ht => by change t < 2 at ht; exact (sub_pos.mpr ht).ne')).sub contDiffOn_const).div_const 15
  have hd₀ : deriv (fun t : ℝ => t / 15) 0 = 1 / 15 := by
    exact ((hasDerivAt_id (0 : ℝ)).div_const 15).deriv
  have hd₁ : deriv (fun t : ℝ => (16 / (2 - t) - 1) / 15) 1 = 16 / 15 := by
    have h := (((hasDerivAt_const (1 : ℝ) 16).div
      ((hasDerivAt_const (1 : ℝ) 2).sub (hasDerivAt_id 1)) (by norm_num)).sub_const 1).div_const 15
    convert h.deriv using 1 <;> norm_num
  obtain ⟨D, hm, hlow, hupp, himg⟩ :=
    DifferentialGeometry.Analysis.exists_diffeomorph_eq_endpoint_germs (a := 0) (b := 1)
      (by norm_num) isOpen_univ (_root_.Set.mem_univ _) h₀ isOpen_Iio (by norm_num) h₁
      (by norm_num) (by norm_num) (by rw [hd₀]; norm_num) (by rw [hd₁]; norm_num)
  exact ⟨D, hm, himg, hlow, hupp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_stereographic_cylinder_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_stereographic_cylinder_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_stereographic_cylinder_reparametrization ``Submission.DifferentialGeometry.Topology.Manifold.exists_stereographic_cylinder_reparametrization


def unitIntervalRestriction (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' _root_.Set.Icc (0 : ℝ) 1 = _root_.Set.Icc (0 : ℝ) 1) :
    Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (_root_.Set.Icc (0 : ℝ) 1) (_root_.Set.Icc (0 : ℝ) 1) ∞ := by
  let H := (D.toHomeomorph.image (_root_.Set.Icc (0 : ℝ) 1)).trans (Homeomorph.setCongr hI)
  have hval (t : _root_.Set.Icc (0 : ℝ) 1) : (H t).val = D t.val := rfl
  have hival (t : _root_.Set.Icc (0 : ℝ) 1) : (H.symm t).val = D.symm t.val := by
    apply D.injective
    change D (H.symm t).val = D (D.symm t.val)
    rw [← hval, Homeomorph.apply_symm_apply, D.apply_symm_apply]
  refine ⟨H.toEquiv, ?_, ?_⟩
  · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨H.continuous, ?_⟩
    exact D.contMDiff.comp contMDiff_subtypeVal_Icc
  · apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨H.symm.continuous, ?_⟩
    exact (D.symm.contMDiff.comp contMDiff_subtypeVal_Icc).congr hival

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.unitIntervalRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.unitIntervalRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.unitIntervalRestriction ``Submission.DifferentialGeometry.Topology.Manifold.unitIntervalRestriction

theorem unitIntervalRestriction_apply (D : ℝ ≃ₘ[ℝ] ℝ)
    (hI : D '' _root_.Set.Icc (0 : ℝ) 1 = _root_.Set.Icc (0 : ℝ) 1) (t : _root_.Set.Icc (0 : ℝ) 1) :
    (unitIntervalRestriction D hI t).val = D t.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.unitIntervalRestriction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.unitIntervalRestriction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.unitIntervalRestriction_apply ``Submission.DifferentialGeometry.Topology.Manifold.unitIntervalRestriction_apply

end DifferentialGeometry.Topology.Manifold
