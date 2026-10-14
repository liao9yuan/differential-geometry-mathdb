import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Topology.Manifold.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
noncomputable def diffeomorphCircle :
    Diffeomorph 𝓘(ℝ, ℝ) (𝓡 1) (AddCircle (1 : ℝ)) Circle ∞ where
  toEquiv := (_root_.AddCircle.homeomorphCircle one_ne_zero).toEquiv
  contMDiff_toFun := by
    apply isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective QuotientAddGroup.mk_surjective
    have heq (t : ℝ) : _root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ)) =
        Circle.exp (2 * Real.pi * t) := by
      rw [_root_.AddCircle.homeomorphCircle_apply, _root_.AddCircle.toCircle_apply_mk]
      congr 1
      ring
    exact (contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff).congr heq
  contMDiff_invFun := by
    have hf : ContMDiff (𝓡 1) (𝓡 1) ∞
        ((_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm : Circle → AddCircle (1 : ℝ)) :=
      DifferentialGeometry.Manifold.contMDiff_homeomorphChartedSpace (𝓡 1)
        (_root_.AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) euclideanSpaceFinOneHomeomorphReal
      euclideanSpaceFinOneContinuousLinearEquivReal (fun _ => rfl) (I₀ := 𝓡 1)).mpr hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.diffeomorphCircle then
    throwError "Refusing to shadow existing declaration AddCircle.diffeomorphCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.diffeomorphCircle ``Submission.AddCircle.diffeomorphCircle

end AddCircle
