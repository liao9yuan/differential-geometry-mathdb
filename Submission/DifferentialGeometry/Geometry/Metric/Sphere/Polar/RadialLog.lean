import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Polar.Bijection
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Intrinsic
import Submission.DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import Submission.DifferentialGeometry.Geometry.Exponential.DiagonalExponential.FixedBasePartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Module _root_.Submission.Module _root_.Set
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialLog (p x : E) : E :=
  (spherePolarInv p x).1 • (spherePolarInv p x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.radialLog then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.radialLog"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.radialLog ``Submission.DifferentialGeometry.Geometry.radialLog

theorem radialLog_smooth (p : E) :
    ContDiffOn ℝ ∞ (radialLog p) {x : E | |⟪p, x⟫_ℝ| < 1} := by
  rw [show radialLog p =
    ((fun x : E ↦ (spherePolarInv p x).1) •
      fun x : E ↦ (spherePolarInv p x).2) by rfl]
  exact (polarInv_smooth p).fst.smul (polarInv_smooth p).snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.radialLog_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.radialLog_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.radialLog_smooth ``Submission.DifferentialGeometry.Geometry.radialLog_smooth

theorem radialLog_orth {p : E} (hp : ‖p‖ = 1) (x : E) :
    ⟪p, radialLog p x⟫_ℝ = 0 := by
  have hpp : ⟪p, p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hp, one_pow]
  simp only [radialLog, spherePolarInv, real_inner_smul_right,
    inner_sub_right, real_inner_smul_right, hpp]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.radialLog_orth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.radialLog_orth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.radialLog_orth ``Submission.DifferentialGeometry.Geometry.radialLog_orth

theorem radialLog_norm
    {p x : E} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1)
    (hxp : x ≠ p) (hxnp : x ≠ -p) :
    ‖radialLog p x‖ = Real.arccos ⟪p, x⟫_ℝ := by
  obtain ⟨hr, _hpw, hwn, _hpolar⟩ := polar_decomp hp hx hxp hxnp
  simp only [radialLog, spherePolarInv, norm_smul, hwn, mul_one]
  rw [Real.norm_eq_abs, abs_of_pos hr.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.radialLog_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.radialLog_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.radialLog_norm ``Submission.DifferentialGeometry.Geometry.radialLog_norm

theorem polar_right_inv
    {p x : E} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1)
    (hxp : x ≠ p) (hxnp : x ≠ -p) :
    spherePolar p (spherePolarInv p x) = x := by
  obtain ⟨_hr, _hpw, _hwn, hpolar⟩ := polar_decomp hp hx hxp hxnp
  simpa only [spherePolarInv] using hpolar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.polar_right_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.polar_right_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.polar_right_inv ``Submission.DifferentialGeometry.Geometry.polar_right_inv

variable [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private instance sphereModel_neZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereModel_neZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereModel_neZero target :: scope.openDecls } }

def roundLog
    (p x : _root_.Metric.sphere (0 : E) 1) : EuclideanSpace ℝ (Fin n) :=
  (dInclEquiv (n := n) p).symm
    (((ℝ ∙ (p : E))ᗮ).orthogonalProjectionOnto (radialLog (p : E) (x : E)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundLog then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundLog"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundLog ``Submission.DifferentialGeometry.Geometry.roundLog

omit [FiniteDimensional ℝ E] [NeZero n] in
theorem roundLog_val
    (p x : _root_.Metric.sphere (0 : E) 1) :
    dIncl (n := n) p (roundLog (n := n) p x) =
      radialLog (p : E) (x : E) := by
  let K : Submodule ℝ E := (ℝ ∙ (p : E))ᗮ
  have hmem : radialLog (p : E) (x : E) ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact radialLog_orth (norm_eq_of_mem_sphere p) (x : E)
  change dIncl (n := n) p
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) p).symm
        (roundLog (n := n) p x)) = radialLog (p : E) (x : E)
  rw [← dInclEquiv_coe (n := n) p]
  change
    (((dInclEquiv (n := n) p)
      ((dInclEquiv (n := n) p).symm
        (K.orthogonalProjectionOnto (radialLog (p : E) (x : E))))) : K) =
      radialLog (p : E) (x : E)
  rw [(dInclEquiv (n := n) p).apply_symm_apply]
  exact congrArg Subtype.val
    (K.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨radialLog (p : E) (x : E), hmem⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundLog_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundLog_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundLog_val ``Submission.DifferentialGeometry.Geometry.roundLog_val

omit [FiniteDimensional ℝ E] [NeZero n] in
@[simp] theorem roundLog_self (p : _root_.Metric.sphere (0 : E) 1) :
    roundLog (n := n) p p = 0 := by
  apply injective_mvfderiv_subtypeVal_sphere p
  change dIncl (n := n) p (roundLog (n := n) p p) =
    dIncl (n := n) p 0
  rw [roundLog_val, map_zero]
  have hpp : ⟪(p : E), (p : E)⟫_ℝ = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
  simp only [radialLog, spherePolarInv, hpp, Real.arccos_one, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundLog_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundLog_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundLog_self ``Submission.DifferentialGeometry.Geometry.roundLog_self

omit [FiniteDimensional ℝ E] [NeZero n] in
theorem roundLog_smooth_off (p : _root_.Metric.sphere (0 : E) 1) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (roundLog (n := n) p) {x | x ≠ p ∧ x ≠ -p} := by
  intro x hx
  have hpNorm : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have hxNorm : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  have habs : |⟪(p : E), (x : E)⟫_ℝ| < 1 := by
    rw [abs_lt]
    constructor
    · have hle :=
        neg_one_le_real_inner_of_norm_eq_one hpNorm hxNorm
      have hne : ⟪(p : E), (x : E)⟫_ℝ ≠ -1 := by
        intro heq
        have hpx :
            (p : E) = -(x : E) :=
          (inner_eq_neg_one_iff_of_norm_eq_one hpNorm hxNorm).mp heq
        have hxp : (x : E) = -(p : E) := by
          have hneg := congrArg Neg.neg hpx
          simpa only [neg_neg] using hneg.symm
        exact hx.2 (Subtype.ext hxp)
      exact lt_of_le_of_ne hle hne.symm
    · exact
        (inner_lt_one_iff_real_of_norm_eq_one hpNorm hxNorm).mpr
          (fun h => hx.1 (Subtype.ext h.symm))
  let A : Set E := {y : E | |⟪(p : E), y⟫_ℝ| < 1}
  have hAopen : IsOpen A := by
    exact isOpen_lt
      ((continuous_const.inner continuous_id).abs) continuous_const
  have hradAt :
      ContDiffAt ℝ ∞ (radialLog (p : E)) (x : E) :=
    (radialLog_smooth (p : E) (x : E) habs).contDiffAt
      (hAopen.mem_nhds habs)
  have hcoe :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
        ((↑) : _root_.Metric.sphere (0 : E) 1 → E) x :=
    (contMDiff_coe_sphere (n := n)).contMDiffAt
  have hrad :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
        (fun y : _root_.Metric.sphere (0 : E) 1 =>
          radialLog (p : E) (y : E)) x :=
    hradAt.contMDiffAt.comp x hcoe
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (dInclEquiv (n := n) p).symm.toContinuousLinearMap.comp
      (((ℝ ∙ (p : E))ᗮ).orthogonalProjectionOnto)
  have hL :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ L :=
    L.contDiff.contMDiff
  rw [show roundLog (n := n) p =
    (fun y : _root_.Metric.sphere (0 : E) 1 ↦ L (radialLog (p : E) (y : E))) by rfl]
  exact (hL.contMDiffAt.comp x hrad).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundLog_smooth_off then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundLog_smooth_off"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundLog_smooth_off ``Submission.DifferentialGeometry.Geometry.roundLog_smooth_off

omit [FiniteDimensional ℝ E] [NeZero n] in
theorem roundLog_tendsto (p : _root_.Metric.sphere (0 : E) 1) :
    Tendsto (roundLog (n := n) p) (𝓝 p) (𝓝 0) := by
  let a : _root_.Metric.sphere (0 : E) 1 → ℝ :=
    fun x => Real.arccos ⟪(p : E), (x : E)⟫_ℝ
  have hinner :
      Continuous (fun x : _root_.Metric.sphere (0 : E) 1 =>
        ⟪(p : E), (x : E)⟫_ℝ) :=
    continuous_const.inner
      (contMDiff_coe_sphere (m := ∞) (n := n)).continuous
  have ha : _root_.Filter.Tendsto a (𝓝 p) (𝓝 0) := by
    have h :=
      (Real.continuous_arccos.comp hinner).continuousAt (x := p)
    have hpp : ⟪(p : E), (p : E)⟫_ℝ = 1 :=
      inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
    rw [show a = Real.arccos ∘
      (fun x : _root_.Metric.sphere (0 : E) 1 ↦ ⟪(p : E), (x : E)⟫_ℝ) by rfl]
    rw [show (0 : ℝ) = Real.arccos ⟪(p : E), (p : E)⟫_ℝ by
      simp only [hpp, Real.arccos_one]]
    exact h
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  have hnotneg : ∀ᶠ x in 𝓝 p, x ≠ -p := by
    have hopen : IsOpen {x : _root_.Metric.sphere (0 : E) 1 | x ≠ -p} := by
      change IsOpen (({-p} : Set (_root_.Metric.sphere (0 : E) 1))ᶜ)
      exact isOpen_compl_singleton
    exact hopen.mem_nhds hpneg
  have hnorm :
      (fun x : _root_.Metric.sphere (0 : E) 1 =>
        ‖radialLog (p : E) (x : E)‖) =ᶠ[𝓝 p] a := by
    filter_upwards [hnotneg] with x hxneg
    by_cases hxp : x = p
    · subst x
      have hpp : ⟪(p : E), (p : E)⟫_ℝ = 1 :=
        inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
      simp only [radialLog, spherePolarInv, hpp, Real.arccos_one,
        zero_smul, norm_zero, a]
    · exact radialLog_norm
        (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere x)
        (fun h => hxp (Subtype.ext h))
        (fun h => hxneg (Subtype.ext h))
  have hrad :
      _root_.Filter.Tendsto (fun x : _root_.Metric.sphere (0 : E) 1 =>
        radialLog (p : E) (x : E)) (𝓝 p) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact ha.congr' hnorm.symm
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (dInclEquiv (n := n) p).symm.toContinuousLinearMap.comp
      (((ℝ ∙ (p : E))ᗮ).orthogonalProjectionOnto)
  have hL : _root_.Filter.Tendsto L (𝓝 0) (𝓝 0) := by
    have hLc : ContinuousAt L 0 := L.continuous.continuousAt
    simpa only [ContinuousAt, map_zero] using hLc
  rw [show roundLog (n := n) p =
    (fun x : _root_.Metric.sphere (0 : E) 1 ↦ L (radialLog (p : E) (x : E))) by rfl]
  rw [show (fun x : _root_.Metric.sphere (0 : E) 1 ↦ L (radialLog (p : E) (x : E))) =
    L ∘ (fun x : _root_.Metric.sphere (0 : E) 1 ↦ radialLog (p : E) (x : E)) by rfl]
  exact hL.comp hrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundLog_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundLog_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundLog_tendsto ``Submission.DifferentialGeometry.Geometry.roundLog_tendsto

variable
  [RiemannianBundle
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]
  [PseudoEMetricSpace (sphere (0 : E) 1)]
  [@CompleteSpace (sphere (0 : E) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : E) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : E) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]

theorem round_exp_log
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p x : _root_.Metric.sphere (0 : E) 1) (hxp : x ≠ p) (hxnp : x ≠ -p) :
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (roundLog (n := n) p x) = x := by
  let r : ℝ := Real.arccos ⟪(p : E), (x : E)⟫_ℝ
  let w : E :=
    (Real.sin r)⁻¹ • ((x : E) - ⟪(p : E), (x : E)⟫_ℝ • (p : E))
  obtain ⟨hr, hpw, hwn, hpolar⟩ :=
    polar_decomp (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere x)
      (fun h => hxp (Subtype.ext h)) (fun h => hxnp (Subtype.ext h))
  have hwmem : w ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hpw
  let v : TangentSpace (𝓡 n) p :=
    (dInclEquiv (n := n) p).symm ⟨w, hwmem⟩
  have hdv : dIncl (n := n) p v = w := by
    rw [← dInclEquiv_coe (n := n) p]
    exact congrArg Subtype.val
      ((dInclEquiv (n := n) p).apply_symm_apply ⟨w, hwmem⟩)
  have hv : ‖dIncl (n := n) p v‖ = 1 := by
    rw [hdv]
    exact hwn
  have hlog : roundLog (n := n) p x = r • v := by
    apply injective_mvfderiv_subtypeVal_sphere p
    change dIncl (n := n) p (roundLog (n := n) p x) =
      dIncl (n := n) p (r • v)
    rw [roundLog_val, map_smul, hdv]
    rfl
  rw [hlog, round_exp_radial hEnorm p v hv r]
  apply Subtype.ext
  simpa only [greatCircle_val, hdv, spherePolar, r, w] using hpolar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.round_exp_log then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.round_exp_log"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.round_exp_log ``Submission.DifferentialGeometry.Geometry.round_exp_log

theorem round_exp_log_ne
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p x : _root_.Metric.sphere (0 : E) 1) (hxnp : x ≠ -p) :
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (roundLog (n := n) p x) = x := by
  by_cases hxp : x = p
  · subst x
    rw [roundLog_self]
    change
      expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (0 : TangentSpace (𝓡 n) p) = p
    exact expMapIntrinsic_zero (roundMetric (E := E) (n := n)) hEnorm p
  · exact round_exp_log hEnorm p x hxp hxnp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.round_exp_log_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.round_exp_log_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.round_exp_log_ne ``Submission.DifferentialGeometry.Geometry.round_exp_log_ne

private theorem log_eq_branch
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : _root_.Metric.sphere (0 : E) 1) :
    roundLog (n := n) p =ᶠ[𝓝 p]
      (standardDiagonalInverseBranch (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p).fixedBasePartialDiffeomorph.symm := by
  let B :=
    standardDiagonalInverseBranch (I := 𝓡 n) (roundMetric (E := E) (n := n)) hEnorm p
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  have hnotneg : ∀ᶠ x in 𝓝 p, x ≠ -p := by
    have hopen : IsOpen {x : _root_.Metric.sphere (0 : E) 1 | x ≠ -p} := by
      change IsOpen (({-p} : Set (_root_.Metric.sphere (0 : E) 1))ᶜ)
      exact isOpen_compl_singleton
    exact hopen.mem_nhds hpneg
  have hsource :
      ∀ᶠ x in 𝓝 p, roundLog (n := n) p x ∈ B.fixedBasePartialDiffeomorph.source :=
    roundLog_tendsto (n := n) p
      (B.fixedBasePartialDiffeomorph.open_source.mem_nhds B.fixedBasePartialDiffeomorph_zero_mem_source)
  filter_upwards [hnotneg, hsource] with x hxneg hxsrc
  by_cases hxp : x = p
  · subst x
    change roundLog (n := n) p p = B.fixedBasePartialDiffeomorph.symm p
    rw [roundLog_self]
    exact B.fixedBasePartialDiffeomorph_symm_center.symm
  · have hexp :=
      round_exp_log hEnorm p x hxp hxneg
    have hmap :
        B.fixedBasePartialDiffeomorph (roundLog (n := n) p x) = x := by
      change expMapIntrinsic (I := 𝓡 n)
          (roundMetric (E := E) (n := n)) hEnorm p
            ((tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) p).symm
              (roundLog (n := n) p x)) = x
      convert hexp using 1
      exact congrArg
        (fun v : TangentSpace (𝓡 n) p =>
          expMapIntrinsic (I := 𝓡 n)
            (roundMetric (E := E) (n := n)) hEnorm p v)
        (tangentSpaceModelContinuousLinearEquiv_symm_apply
          (I := 𝓡 n) p (roundLog (n := n) p x))
    have hleft := B.fixedBasePartialDiffeomorph.left_inv hxsrc
    rw [hmap] at hleft
    exact hleft.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.log_eq_branch
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.log_eq_branch target :: scope.openDecls } }

theorem roundLog_smooth
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : _root_.Metric.sphere (0 : E) 1) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (roundLog (n := n) p) {x | x ≠ -p} := by
  let B :=
    standardDiagonalInverseBranch (I := 𝓡 n) (roundMetric (E := E) (n := n)) hEnorm p
  intro x hx
  by_cases hxp : x = p
  · subst x
    have hB :
        ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
          B.fixedBasePartialDiffeomorph.symm p :=
      B.fixedBasePartialDiffeomorph.symm.contMDiffOn_toFun.contMDiffAt
        (B.fixedBasePartialDiffeomorph.open_target.mem_nhds B.fixedBasePartialDiffeomorph_center_mem_target)
    exact
      (hB.congr_of_eventuallyEq
        (log_eq_branch (n := n) hEnorm p)).contMDiffWithinAt
  · have hoff :
        ContMDiffWithinAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
          (roundLog (n := n) p) {y | y ≠ p ∧ y ≠ -p} x :=
      roundLog_smooth_off (n := n) p x ⟨hxp, hx⟩
    have hopen : IsOpen {y : _root_.Metric.sphere (0 : E) 1 | y ≠ p ∧ y ≠ -p} := by
      change IsOpen
        (({p} : Set (_root_.Metric.sphere (0 : E) 1))ᶜ ∩
          (({-p} : Set (_root_.Metric.sphere (0 : E) 1))ᶜ))
      exact isOpen_compl_singleton.inter isOpen_compl_singleton
    exact (hoff.contMDiffAt (hopen.mem_nhds ⟨hxp, hx⟩)).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundLog_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundLog_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundLog_smooth ``Submission.DifferentialGeometry.Geometry.roundLog_smooth

theorem roundLog_mfd_self
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : _root_.Metric.sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (roundLog (n := n) p) p =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  let logf : _root_.Metric.sphere (0 : E) 1 → EuclideanSpace ℝ (Fin n) :=
    roundLog (n := n) p
  let expf : EuclideanSpace ℝ (Fin n) → _root_.Metric.sphere (0 : E) 1 := fun u =>
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
      hEnorm p (show TangentSpace (𝓡 n) p from u)
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  have hUopen : IsOpen {x : _root_.Metric.sphere (0 : E) 1 | x ≠ -p} := by
    change IsOpen (({-p} : Set (_root_.Metric.sphere (0 : E) 1))ᶜ)
    exact isOpen_compl_singleton
  have hlog :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) logf p :=
    ((roundLog_smooth hEnorm p).contMDiffAt
      (hUopen.mem_nhds hpneg)).mdifferentiableAt (by simp)
  have hexp :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
        expf (logf p) := by
    exact (intrinsicFiber_smooth (I := 𝓡 n)
      (roundMetric (E := E) (n := n)) hEnorm p).contMDiffAt.mdifferentiableAt
        (by simp)
  have hident : (expf ∘ logf) =ᶠ[𝓝 p] id := by
    refine _root_.Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpneg) ?_
    intro x hx
    simpa only [expf, logf, Function.comp_apply, id_eq] using
      round_exp_log_ne hEnorm p x hx
  have hchain :=
    mfderiv_comp
      (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I'' := 𝓡 n) p hexp hlog
  have hid := Filter.EventuallyEq.mfderiv_eq
    (I := 𝓡 n) (I' := 𝓡 n) hident
  have hp0 : logf p = 0 := by
    simp only [logf, roundLog_self]
  have hexp0 :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf 0 =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [expf] using
      mfderiv_expMapIntrinsic_at_zero (I := 𝓡 n)
        (roundMetric (E := E) (n := n)) hEnorm p
  apply ContinuousLinearMap.ext
  intro v
  have hv := DFunLike.congr_fun hid v
  rw [hchain, mfderiv_id] at hv
  change
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf (logf p)
        (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) logf p v) = v at hv
  rw [hp0, hexp0] at hv
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (roundLog (n := n) p p)).injective
  have hvModel := congrArg
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (expf 0)) hv
  have hvModel' := hvModel.trans
    (tangentSpaceModelContinuousLinearEquiv_apply (I := 𝓡 n) (expf 0) v)
  have hvModelNormalized :=
    (tangentSpaceModelContinuousLinearEquiv_apply (I := 𝓡 n) (expf 0)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
        (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) logf p v))).symm.trans
      hvModel'
  change mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (roundLog (n := n) p) p v =
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) v
  have hvModel'' :
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
          (show EuclideanSpace ℝ (Fin n) from
            mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              (roundLog (n := n) p) p v) =
        (show EuclideanSpace ℝ (Fin n) from v) := by
    simpa only [logf] using hvModelNormalized
  exact (by rfl :
      (show EuclideanSpace ℝ (Fin n) from
        mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (roundLog (n := n) p) p v) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
        (show EuclideanSpace ℝ (Fin n) from
          mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (roundLog (n := n) p) p v)).trans
      (hvModel''.trans (by rfl))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundLog_mfd_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundLog_mfd_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundLog_mfd_self ``Submission.DifferentialGeometry.Geometry.roundLog_mfd_self

end Geometry
end DifferentialGeometry
