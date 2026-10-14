import Mathlib.Analysis.InnerProductSpace.LaxMilgram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
namespace DifferentialGeometry

open _root_.RealInnerProductSpace

class CoerciveBilinInverse (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] : Prop where
  surjective : ∀ {B : E →L[Real] E →L[Real] Real},
    IsCoercive B → Function.Surjective B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CoerciveBilinInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CoerciveBilinInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CoerciveBilinInverse ``Submission.DifferentialGeometry.CoerciveBilinInverse

class ContinuousDualEquiv (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] where
  equiv : E ≃L[Real] (E →L[Real] Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ContinuousDualEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ContinuousDualEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ContinuousDualEquiv ``Submission.DifferentialGeometry.ContinuousDualEquiv

namespace ContinuousDualEquiv

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
  [ContinuousDualEquiv E]

noncomputable def normalization : Realˣ :=
  Units.mk0
    (1 + ‖((equiv (E := E)).symm : (E →L[Real] Real) →L[Real] E)‖)
    (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ContinuousDualEquiv.normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ContinuousDualEquiv.normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ContinuousDualEquiv.normalization ``Submission.DifferentialGeometry.ContinuousDualEquiv.normalization

noncomputable def normalizedEquiv : E ≃L[Real] (E →L[Real] Real) :=
  (ContinuousLinearEquiv.smulLeft (R₁ := Real) (M₁ := E)
      (normalization E)).trans (equiv (E := E))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv ``Submission.DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv

theorem normalizedEquiv_symm_apply (eta : E →L[Real] Real) :
    (normalizedEquiv E).symm eta =
      (1 + ‖((equiv (E := E)).symm :
        (E →L[Real] Real) →L[Real] E)‖)⁻¹ •
        (equiv (E := E)).symm eta := by
  let s := ContinuousLinearEquiv.smulLeft (R₁ := Real) (M₁ := E)
    (normalization E)
  change s.symm ((equiv (E := E)).symm eta) = _
  apply s.injective
  rw [s.apply_symm_apply]
  simp only [s, normalization, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_def, Units.val_mk0]
  exact (smul_inv_smul₀ (by positivity) _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_apply ``Submission.DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_apply

theorem normalizedEquiv_symm_norm_le_one :
    ‖((normalizedEquiv E).symm :
      (E →L[Real] Real) →L[Real] E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro eta
  change ‖(normalizedEquiv E).symm eta‖ ≤ _
  rw [normalizedEquiv_symm_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
  have he := ContinuousLinearMap.le_opNorm
    ((equiv (E := E)).symm : (E →L[Real] Real) →L[Real] E) eta
  calc
    (1 + ‖((equiv (E := E)).symm :
        (E →L[Real] Real) →L[Real] E)‖)⁻¹ *
        ‖(equiv (E := E)).symm eta‖ ≤
      (1 + ‖((equiv (E := E)).symm :
          (E →L[Real] Real) →L[Real] E)‖)⁻¹ *
        (‖((equiv (E := E)).symm :
          (E →L[Real] Real) →L[Real] E)‖ * ‖eta‖) :=
      mul_le_mul_of_nonneg_left (by simpa using he) (by positivity)
    _ ≤ 1 * ‖eta‖ := by
      have h :
          (1 + ‖((equiv (E := E)).symm :
              (E →L[Real] Real) →L[Real] E)‖)⁻¹ *
            ‖((equiv (E := E)).symm :
              (E →L[Real] Real) →L[Real] E)‖ ≤ 1 := by
        rw [inv_mul_le_one₀ (by positivity)]
        linarith [norm_nonneg
          ((equiv (E := E)).symm :
            (E →L[Real] Real) →L[Real] E)]
      nlinarith [norm_nonneg eta]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_norm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_norm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_norm_le_one ``Submission.DifferentialGeometry.ContinuousDualEquiv.normalizedEquiv_symm_norm_le_one

end ContinuousDualEquiv
end DifferentialGeometry

namespace IsCoercive
open _root_.IsCoercive
open _root_.Submission.DifferentialGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
open _root_.IsCoercive in
instance _root_.Submission.IsCoercive.instFiniteDimensionalRealStrongDual_differentialGeometry [FiniteDimensional Real E] : FiniteDimensional Real (StrongDual Real E) :=
  inferInstanceAs (FiniteDimensional Real (E →L[Real] Real))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.instFiniteDimensionalRealStrongDual_differentialGeometry then
    throwError "Refusing to shadow existing declaration IsCoercive.instFiniteDimensionalRealStrongDual_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.instFiniteDimensionalRealStrongDual_differentialGeometry ``Submission.IsCoercive.instFiniteDimensionalRealStrongDual_differentialGeometry

open _root_.IsCoercive in
theorem bilin_injective {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : Function.Injective B := by
  intro u v huv
  rcases hco with ⟨c, hc, hB⟩
  have hzeroMap : B (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hbound := hB (u - v)
  have hzero : B (u - v) (u - v) = 0 := by rw [hzeroMap]; rfl
  rw [hzero] at hbound
  have hsub : u - v = 0 := by
    by_contra hne
    have hn : 0 < ‖u - v‖ := norm_pos_iff.mpr hne
    exact (not_lt_of_ge hbound) (mul_pos (mul_pos hc hn) hn)
  exact sub_eq_zero.mp hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.bilin_injective then
    throwError "Refusing to shadow existing declaration IsCoercive.bilin_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.bilin_injective ``Submission.IsCoercive.bilin_injective

open _root_.IsCoercive in
noncomputable instance coerciveBilinInverseOfFiniteDimensional
    [FiniteDimensional Real E] : CoerciveBilinInverse E where
  surjective := by
    intro B hco
    exact (LinearEquiv.ofInjectiveOfFinrankEq B.toLinearMap
      (bilin_injective hco) (by
        rw [← LinearEquiv.finrank_eq LinearMap.toContinuousLinearMap]
        exact Subspace.dual_finrank_eq.symm)).surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.coerciveBilinInverseOfFiniteDimensional then
    throwError "Refusing to shadow existing declaration IsCoercive.coerciveBilinInverseOfFiniteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.coerciveBilinInverseOfFiniteDimensional ``Submission.IsCoercive.coerciveBilinInverseOfFiniteDimensional

open _root_.IsCoercive in
noncomputable instance continuousDualEquivOfFiniteDimensional
    [FiniteDimensional Real E] : ContinuousDualEquiv E where
  equiv := ContinuousLinearEquiv.ofFinrankEq (by
    rw [← LinearEquiv.finrank_eq LinearMap.toContinuousLinearMap]
    exact Subspace.dual_finrank_eq.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.continuousDualEquivOfFiniteDimensional then
    throwError "Refusing to shadow existing declaration IsCoercive.continuousDualEquivOfFiniteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.continuousDualEquivOfFiniteDimensional ``Submission.IsCoercive.continuousDualEquivOfFiniteDimensional

open _root_.IsCoercive in
noncomputable instance (priority := 900) coerciveBilinInverseOfInnerProduct
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] : CoerciveBilinInverse F where
  surjective := by
    intro B hco eta
    refine ⟨hco.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual Real F).symm eta), ?_⟩
    apply ContinuousLinearMap.ext
    intro w
    rw [← hco.continuousLinearEquivOfBilin_apply]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.coerciveBilinInverseOfInnerProduct then
    throwError "Refusing to shadow existing declaration IsCoercive.coerciveBilinInverseOfInnerProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.coerciveBilinInverseOfInnerProduct ``Submission.IsCoercive.coerciveBilinInverseOfInnerProduct

open _root_.IsCoercive in
noncomputable instance (priority := 900) continuousDualEquivOfInnerProduct
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] : ContinuousDualEquiv F where
  equiv := (InnerProductSpace.toDual Real F).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.continuousDualEquivOfInnerProduct then
    throwError "Refusing to shadow existing declaration IsCoercive.continuousDualEquivOfInnerProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.continuousDualEquivOfInnerProduct ``Submission.IsCoercive.continuousDualEquivOfInnerProduct

variable [CompleteSpace E] [CoerciveBilinInverse E]

open _root_.IsCoercive in
theorem symm_norm_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] {B : F →L[Real] F →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : F, c * ‖v‖ * ‖v‖ ≤ B v v) (xi : F) :
    ‖hco.continuousLinearEquivOfBilin.symm xi‖ ≤ c⁻¹ * ‖xi‖ := by
  let u := hco.continuousLinearEquivOfBilin.symm xi
  have heu : hco.continuousLinearEquivOfBilin u = xi :=
    hco.continuousLinearEquivOfBilin.apply_symm_apply xi
  change ‖u‖ ≤ c⁻¹ * ‖xi‖
  by_cases hu : u = 0
  · rw [hu, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg xi)
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcu : c * ‖u‖ ≤ ‖xi‖ := by
      refine le_of_mul_le_mul_right ?_ hupos
      calc
        c * ‖u‖ * ‖u‖ ≤ B u u := hB u
        _ = _root_.Inner.inner Real (hco.continuousLinearEquivOfBilin u) u :=
          (hco.continuousLinearEquivOfBilin_apply u u).symm
        _ = _root_.Inner.inner Real xi u := by rw [heu]
        _ ≤ ‖xi‖ * ‖u‖ := real_inner_le_norm xi u
    calc
      ‖u‖ ≤ ‖xi‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcu)
      _ = c⁻¹ * ‖xi‖ := by rw [div_eq_mul_inv, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.symm_norm_le then
    throwError "Refusing to shadow existing declaration IsCoercive.symm_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.symm_norm_le ``Submission.IsCoercive.symm_norm_le

open _root_.IsCoercive in
private noncomputable def toDualEquiv {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : E ≃L[Real] (E →L[Real] Real) :=
  ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr (bilin_injective hco))
    (LinearMap.range_eq_top.mpr (CoerciveBilinInverse.surjective hco))

run_cmd do
  let target := ``Submission.IsCoercive.toDualEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `IsCoercive.toDualEquiv target :: scope.openDecls } }

open _root_.IsCoercive in
noncomputable def sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) : E :=
  (toDualEquiv hco).symm eta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharp then
    throwError "Refusing to shadow existing declaration IsCoercive.sharp"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharp ``Submission.IsCoercive.sharp

open _root_.IsCoercive in
theorem sharp_eq_inverse
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F]
    {B : F →L[Real] F →L[Real] Real}
    (hco : IsCoercive B) (eta : F →L[Real] Real) :
    hco.sharp eta =
      Ring.inverse (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B)
        ((InnerProductSpace.toDual Real F).symm eta) := by
  have heq : hco.sharp eta = hco.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual Real F).symm eta) := by
    apply bilin_injective hco
    change B ((toDualEquiv hco).symm eta) = _
    have hlhs := (toDualEquiv hco).apply_symm_apply eta
    change B ((toDualEquiv hco).symm eta) = eta at hlhs
    rw [hlhs]
    symm
    apply ContinuousLinearMap.ext
    intro w
    rw [← hco.continuousLinearEquivOfBilin_apply]
    simp
  rw [heq]
  change hco.continuousLinearEquivOfBilin.symm _ =
    Ring.inverse
      (↑hco.continuousLinearEquivOfBilin.toUnit : F →L[Real] F) _
  rw [Ring.inverse_unit]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharp_eq_inverse then
    throwError "Refusing to shadow existing declaration IsCoercive.sharp_eq_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharp_eq_inverse ``Submission.IsCoercive.sharp_eq_inverse

open _root_.IsCoercive in
@[simp] theorem apply_sharp {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    B (hco.sharp eta) = eta := by
  exact (toDualEquiv hco).apply_symm_apply eta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.apply_sharp then
    throwError "Refusing to shadow existing declaration IsCoercive.apply_sharp"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.apply_sharp ``Submission.IsCoercive.apply_sharp

open _root_.IsCoercive in
@[simp] theorem sharp_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (u : E) :
    hco.sharp (B u) = u := by
  exact (toDualEquiv hco).symm_apply_apply u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharp_apply then
    throwError "Refusing to shadow existing declaration IsCoercive.sharp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharp_apply ``Submission.IsCoercive.sharp_apply

open _root_.IsCoercive in
theorem sharp_sub {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta theta : E →L[Real] Real) :
    hco.sharp (eta - theta) = hco.sharp eta - hco.sharp theta := by
  simp [sharp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharp_sub then
    throwError "Refusing to shadow existing declaration IsCoercive.sharp_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharp_sub ``Submission.IsCoercive.sharp_sub

open _root_.IsCoercive in
theorem sharp_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) (eta : E →L[Real] Real) :
    ‖hco.sharp eta‖ ≤ c⁻¹ * ‖eta‖ := by
  let u := hco.sharp eta
  have heu : B u = eta := hco.apply_sharp eta
  by_cases hu : u = 0
  · change ‖u‖ ≤ c⁻¹ * ‖eta‖
    rw [hu, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg eta)
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcu : c * ‖u‖ ≤ ‖eta‖ := by
      refine le_of_mul_le_mul_right ?_ hupos
      calc
        c * ‖u‖ * ‖u‖ ≤ B u u := hB u
        _ = eta u := by rw [heu]
        _ ≤ ‖eta u‖ := by simpa [Real.norm_eq_abs] using le_abs_self (eta u)
        _ ≤ ‖eta‖ * ‖u‖ := eta.le_opNorm u
    calc
      ‖u‖ ≤ ‖eta‖ / c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hcu)
      _ = c⁻¹ * ‖eta‖ := by rw [div_eq_mul_inv, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharp_norm_le then
    throwError "Refusing to shadow existing declaration IsCoercive.sharp_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharp_norm_le ``Submission.IsCoercive.sharp_norm_le

open _root_.IsCoercive in
noncomputable def sharpCLM {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) : (E →L[Real] Real) →L[Real] E :=
  (toDualEquiv hco).symm.toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharpCLM then
    throwError "Refusing to shadow existing declaration IsCoercive.sharpCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharpCLM ``Submission.IsCoercive.sharpCLM
open _root_.IsCoercive in
@[simp] theorem sharpCLM_apply {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) (eta : E →L[Real] Real) :
    hco.sharpCLM eta = hco.sharp eta := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharpCLM_apply then
    throwError "Refusing to shadow existing declaration IsCoercive.sharpCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharpCLM_apply ``Submission.IsCoercive.sharpCLM_apply

open _root_.IsCoercive in
theorem sharpCLM_norm_le {B : E →L[Real] E →L[Real] Real}
    (hco : IsCoercive B) {c : Real} (hc : 0 < c)
    (hB : ∀ v : E, c * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖hco.sharpCLM‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) ?_
  intro eta
  rw [sharpCLM_apply]
  exact hco.sharp_norm_le hc hB eta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharpCLM_norm_le then
    throwError "Refusing to shadow existing declaration IsCoercive.sharpCLM_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharpCLM_norm_le ``Submission.IsCoercive.sharpCLM_norm_le
open _root_.IsCoercive in
noncomputable def gramCLM
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] :
    (F →L[Real] F →L[Real] Real) →L[Real] (F →L[Real] F) :=
  ContinuousLinearMap.compL Real F (F →L[Real] Real) F
    (InnerProductSpace.toDual Real F).symm.toContinuousLinearEquiv.toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.gramCLM then
    throwError "Refusing to shadow existing declaration IsCoercive.gramCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.gramCLM ``Submission.IsCoercive.gramCLM
open _root_.IsCoercive in
@[simp] theorem gramCLM_apply
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] (B : F →L[Real] F →L[Real] Real) :
    gramCLM B = InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.gramCLM_apply then
    throwError "Refusing to shadow existing declaration IsCoercive.gramCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.gramCLM_apply ``Submission.IsCoercive.gramCLM_apply
open _root_.IsCoercive in
theorem gramCLM_isUnit
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F] {B : F →L[Real] F →L[Real] Real} (hB : IsCoercive B) :
    IsUnit (gramCLM B) := by
  rw [gramCLM_apply]
  exact ⟨hB.continuousLinearEquivOfBilin.toUnit, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.gramCLM_isUnit then
    throwError "Refusing to shadow existing declaration IsCoercive.gramCLM_isUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.gramCLM_isUnit ``Submission.IsCoercive.gramCLM_isUnit

open _root_.IsCoercive in
theorem sharpCLM_contOn
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F]
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (B : X → F →L[Real] F →L[Real] Real)
    (hB : ContinuousOn B S) (hco : ∀ x, IsCoercive (B x)) :
    ContinuousOn (fun x => (hco x).sharpCLM) S := by
  let G : (F →L[Real] F →L[Real] Real) →L[Real] (F →L[Real] F) := gramCLM
  have hG : ContinuousOn (fun x => G (B x)) S :=
    G.continuous.comp_continuousOn hB
  have hinv : ContinuousOn (fun x => Ring.inverse (G (B x))) S := by
    intro x hx
    obtain ⟨u, hu⟩ := gramCLM_isUnit (hco x)
    have hri : ContinuousAt (fun A : F →L[Real] F => Ring.inverse A) (G (B x)) := by
      rw [show G (B x) = (u : F →L[Real] F) from hu.symm]
      exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp_continuousWithinAt (f := fun y => G (B y)) hri (hG x hx)
  let R : (F →L[Real] Real) →L[Real] F :=
    (InnerProductSpace.toDual Real F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcomp : ContinuousOn
      (fun x => (Ring.inverse (G (B x))).comp R) S := by
    have hleft : ContinuousOn
        (fun x => ContinuousLinearMap.compL Real (F →L[Real] Real) F F
          (Ring.inverse (G (B x)))) S :=
      (ContinuousLinearMap.compL Real (F →L[Real] Real) F F).continuous.comp_continuousOn
        hinv
    simpa only [ContinuousLinearMap.compL_apply] using
      hleft.clm_apply (continuousOn_const : ContinuousOn (fun _ : X => R) S)
  refine hcomp.congr ?_
  intro x hx
  apply ContinuousLinearMap.ext
  intro eta
  rw [sharpCLM_apply, sharp_eq_inverse]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharpCLM_contOn then
    throwError "Refusing to shadow existing declaration IsCoercive.sharpCLM_contOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharpCLM_contOn ``Submission.IsCoercive.sharpCLM_contOn

open _root_.IsCoercive in
theorem sharpCLM_cont_sub
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [CompleteSpace F]
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (B : X → F →L[Real] F →L[Real] Real)
    (hB : ContinuousOn B S)
    (hco : ∀ x ∈ S, IsCoercive (B x)) :
    Continuous (fun x : S => (hco x x.2).sharpCLM) := by
  have hsub : ContinuousOn
      (fun x : S => B x) (Set.univ : Set S) := hB.domRestrict.continuousOn
  have h := sharpCLM_contOn (fun x : S => B x) hsub
    (fun x => hco x x.2)
  exact continuousOn_univ.mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharpCLM_cont_sub then
    throwError "Refusing to shadow existing declaration IsCoercive.sharpCLM_cont_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharpCLM_cont_sub ``Submission.IsCoercive.sharpCLM_cont_sub

open _root_.IsCoercive in
theorem sharp_sub_le
    {B C : E →L[Real] E →L[Real] Real}
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    {cB cC : Real} (hcB : 0 < cB) (hcC : 0 < cC)
    (hB : ∀ u : E, cB * ‖u‖ * ‖u‖ ≤ B u u)
    (hC : ∀ u : E, cC * ‖u‖ * ‖u‖ ≤ C u u)
    (eta : E →L[Real] Real) :
    ‖hBco.sharp eta - hCco.sharp eta‖ ≤
      cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
  have heq :
      hBco.sharp eta - hCco.sharp eta =
        hBco.sharp ((C - B) (hCco.sharp eta)) := by
    calc
      hBco.sharp eta - hCco.sharp eta =
          hBco.sharp (B (hBco.sharp eta - hCco.sharp eta)) :=
        (hBco.sharp_apply _).symm
      _ = hBco.sharp (B (hBco.sharp eta) - B (hCco.sharp eta)) := by
        rw [map_sub]
      _ = hBco.sharp (eta - B (hCco.sharp eta)) := by
        rw [hBco.apply_sharp]
      _ = hBco.sharp (C (hCco.sharp eta) - B (hCco.sharp eta)) := by
        rw [hCco.apply_sharp]
      _ = hBco.sharp ((C - B) (hCco.sharp eta)) := by
        rw [sub_apply]
  rw [heq]
  calc
    ‖hBco.sharp ((C - B) (hCco.sharp eta))‖ ≤
        cB⁻¹ * ‖(C - B) (hCco.sharp eta)‖ :=
      hBco.sharp_norm_le hcB hB _
    _ ≤ cB⁻¹ * (‖C - B‖ * ‖hCco.sharp eta‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm (C - B) (hCco.sharp eta)
    _ ≤ cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖eta‖)) := by
      gcongr
      exact hCco.sharp_norm_le hcC hC eta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharp_sub_le then
    throwError "Refusing to shadow existing declaration IsCoercive.sharp_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharp_sub_le ``Submission.IsCoercive.sharp_sub_le

open _root_.IsCoercive in
theorem sharp_var_le
    {B C : E →L[Real] E →L[Real] Real}
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    {cB cC : Real} (hcB : 0 < cB) (hcC : 0 < cC)
    (hB : ∀ u : E, cB * ‖u‖ * ‖u‖ ≤ B u u)
    (hC : ∀ u : E, cC * ‖u‖ * ‖u‖ ≤ C u u)
    (eta theta : E →L[Real] Real) :
    ‖hBco.sharp eta - hCco.sharp theta‖ ≤
      cB⁻¹ * ‖eta - theta‖ +
        cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖theta‖)) := by
  have hsplit :
      hBco.sharp eta - hCco.sharp theta =
        (hBco.sharp eta - hBco.sharp theta) +
          (hBco.sharp theta - hCco.sharp theta) := by
    abel
  rw [hsplit]
  calc
    ‖(hBco.sharp eta - hBco.sharp theta) +
        (hBco.sharp theta - hCco.sharp theta)‖ ≤
        ‖hBco.sharp eta - hBco.sharp theta‖ +
          ‖hBco.sharp theta - hCco.sharp theta‖ := norm_add_le _ _
    _ ≤ cB⁻¹ * ‖eta - theta‖ +
        cB⁻¹ * (‖C - B‖ * (cC⁻¹ * ‖theta‖)) := by
      apply add_le_add
      · rw [← hBco.sharp_sub]
        exact hBco.sharp_norm_le hcB hB (eta - theta)
      · exact hBco.sharp_sub_le hCco hcB hcC hB hC theta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoercive.sharp_var_le then
    throwError "Refusing to shadow existing declaration IsCoercive.sharp_var_le"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoercive.sharp_var_le ``Submission.IsCoercive.sharp_var_le

end IsCoercive
