import Submission.DifferentialGeometry.Topology.Manifold.Interval.Tangent
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Function _root_.Bundle _root_.Manifold
open scoped _root_.ContDiff _root_.Topology
noncomputable section
namespace DifferentialGeometry.Manifold.Interval

theorem contMDiff_tangentCoordinateIcc_symm
    {a b : ℝ} [Fact (a < b)] :
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 1).tangent ∞
      (fun q : _root_.Set.Icc a b × ℝ =>
        (⟨q.1, (tangentCoordinateIcc q.1).symm q.2⟩ : TangentBundle (𝓡∂ 1) (_root_.Set.Icc a b))) := by
  have hinput : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent ∞
      (fun q : _root_.Set.Icc a b × ℝ => (⟨q.1.val, q.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro q
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨(contMDiff_subtypeVal_Icc.comp contMDiff_fst) q, ?_⟩
    convert (contMDiff_snd (I := 𝓡∂ 1) (J := 𝓘(ℝ, ℝ)) (M := _root_.Set.Icc a b) (N := ℝ) q) using 1
    simp only [mfld_simps]
  have hproj := (contMDiffOn_projIcc (x := a) (y := b) (n := ∞)).contMDiffOn_tangentMapWithin
    (m := ∞) (by simp) (uniqueDiffOn_Icc (Fact.out : a < b)).uniqueMDiffOn
  have hh := hproj.comp_contMDiff hinput (fun q => q.1.property)
  apply hh.congr
  intro q
  rw [tangentCoordinateIcc_symm_apply]
  simp only [Function.comp_apply, tangentMapWithin]
  apply TotalSpace.ext
  · exact (_root_.Set.projIcc_of_mem (Fact.out : a < b).le q.1.property).symm
  · change HEq (q.2 • (1 : TangentSpace (𝓡∂ 1) q.1))
      (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) (_root_.Set.projIcc a b (Fact.out : a < b).le) (_root_.Set.Icc a b) q.1.val q.2)
    have hlin : mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1)
        (_root_.Set.projIcc a b (Fact.out : a < b).le) (_root_.Set.Icc a b) q.1.val q.2 =
        q.2 • (1 : TangentSpace (𝓡∂ 1) (_root_.Set.projIcc a b (Fact.out : a < b).le q.1.val)) := by
      have hr : (q.2 : TangentSpace 𝓘(ℝ, ℝ) q.1.val) =
          q.2 • (1 : TangentSpace 𝓘(ℝ, ℝ) q.1.val) := by
        change q.2 = q.2 * 1
        exact (mul_one _).symm
      conv_lhs => rw [hr]
      rw [map_smul, mfderivWithin_projIcc_one q.1.property]
    rw [hlin, _root_.Set.projIcc_of_mem (Fact.out : a < b).le q.1.property]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm ``Submission.DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm

def tangentBundleIccDiffeomorph {a b : ℝ} [Fact (a < b)] :
    Diffeomorph (𝓡∂ 1).tangent ((𝓡∂ 1).prod 𝓘(ℝ, ℝ))
      (TangentBundle (𝓡∂ 1) (_root_.Set.Icc a b)) (_root_.Set.Icc a b × ℝ) ∞ where
  toFun p := (p.proj, tangentCoordinateIcc p.proj p.2)
  invFun q := ⟨q.1, (tangentCoordinateIcc q.1).symm q.2⟩
  left_inv p := by
    change (⟨p.proj, (tangentCoordinateIcc p.proj).symm (tangentCoordinateIcc p.proj p.2)⟩ :
      TangentBundle (𝓡∂ 1) (_root_.Set.Icc a b)) = p
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv q := Prod.ext rfl ((tangentCoordinateIcc q.1).apply_symm_apply q.2)
  contMDiff_toFun := (_root_.Bundle.contMDiff_proj (TangentSpace (𝓡∂ 1))).prodMk contMDiff_tangentCoordinateIcc
  contMDiff_invFun := contMDiff_tangentCoordinateIcc_symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph ``Submission.DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph


theorem tangentBundleIccDiffeomorph_apply {a b : ℝ} [Fact (a < b)]
    (p : TangentBundle (𝓡∂ 1) (_root_.Set.Icc a b)) :
    tangentBundleIccDiffeomorph p = (p.proj, tangentCoordinateIcc p.proj p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_apply ``Submission.DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_apply


theorem tangentBundleIccDiffeomorph_symm_apply {a b : ℝ} [Fact (a < b)]
    (q : _root_.Set.Icc a b × ℝ) :
    tangentBundleIccDiffeomorph.symm q =
      (⟨q.1, q.2 • (1 : TangentSpace (𝓡∂ 1) q.1)⟩ : TangentBundle (𝓡∂ 1) (_root_.Set.Icc a b)) := by
  change (⟨q.1, (tangentCoordinateIcc q.1).symm q.2⟩ : TangentBundle (𝓡∂ 1) (_root_.Set.Icc a b)) = _
  rw [tangentCoordinateIcc_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Manifold.Interval.tangentBundleIccDiffeomorph_symm_apply

end DifferentialGeometry.Manifold.Interval
