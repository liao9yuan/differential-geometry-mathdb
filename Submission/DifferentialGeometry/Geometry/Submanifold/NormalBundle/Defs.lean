import Submission.DifferentialGeometry.Geometry.Submanifold.IsometricImmersion
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Logic.Equiv.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry
namespace IsRiemannianIsometricImmersion

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def normalSpaceAt
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (_h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    Submodule ℝ (TangentSpace I (iota x)) :=
  (gM.inner (iota x)).toBilinForm.orthogonal
    (mfderiv IN I iota x).range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem mem_normalSpaceAt_iff
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (v : TangentSpace I (iota x)) :
    v ∈ h.normalSpaceAt x ↔
      ∀ u : TangentSpace IN x,
        gM.inner (iota x) v (mfderiv IN I iota x u) = 0 := by
  rw [normalSpaceAt, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hv u
    rw [gM.symm]
    exact hv (mfderiv IN I iota x u) ⟨u, rfl⟩
  · intro hv w hw
    obtain ⟨u, rfl⟩ := hw
    change gM.inner (iota x) (mfderiv IN I iota x u) v = 0
    rw [gM.symm]
    exact hv u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mem_normalSpaceAt_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mem_normalSpaceAt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mem_normalSpaceAt_iff ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mem_normalSpaceAt_iff

abbrev NormalBundleTotalSpace
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :=
  Σ x : N, h.normalSpaceAt x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.NormalBundleTotalSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.NormalBundleTotalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.NormalBundleTotalSpace ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.NormalBundleTotalSpace

def normalBundleProjection
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    h.NormalBundleTotalSpace → N :=
  Sigma.fst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection

def normalZeroSection
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    N → h.NormalBundleTotalSpace :=
  fun x ↦ ⟨x, 0⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
@[simp]
theorem normalBundleProjection_normalZeroSection
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    h.normalBundleProjection (h.normalZeroSection x) = x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection_normalZeroSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection_normalZeroSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection_normalZeroSection ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleProjection_normalZeroSection

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem normalZeroSection_injective
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    Function.Injective h.normalZeroSection :=
  Function.LeftInverse.injective (h.normalBundleProjection_normalZeroSection)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection_injective ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalZeroSection_injective

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem nonempty_normalBundleTotalSpace_iff
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    Nonempty h.NormalBundleTotalSpace ↔ Nonempty N := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.1⟩
  · rintro ⟨x⟩
    exact ⟨h.normalZeroSection x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.nonempty_normalBundleTotalSpace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.nonempty_normalBundleTotalSpace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.nonempty_normalBundleTotalSpace_iff ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.nonempty_normalBundleTotalSpace_iff

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem normalSpaceAt_eq_top_of_derivative_eq_zero
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (hzero : mfderiv IN I iota x = 0) :
    h.normalSpaceAt x = ⊤ := by
  ext v
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    rw [h.mem_normalSpaceAt_iff]
    intro u
    rw [hzero]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_top_of_derivative_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_top_of_derivative_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_top_of_derivative_eq_zero ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_top_of_derivative_eq_zero

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem range_inf_normalSpaceAt_eq_bot
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    (mfderiv IN I iota x).range ⊓ h.normalSpaceAt x = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨hvRange, hvNormal⟩ := hv
    obtain ⟨u, rfl⟩ := hvRange
    have huOrth := (h.mem_normalSpaceAt_iff x _).mp hvNormal u
    by_contra hv0
    have hpos := gM.pos (iota x) (mfderiv IN I iota x u) hv0
    exact hpos.ne' huOrth
  · exact bot_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.range_inf_normalSpaceAt_eq_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.range_inf_normalSpaceAt_eq_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.range_inf_normalSpaceAt_eq_bot ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.range_inf_normalSpaceAt_eq_bot

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
theorem normalSpaceAt_eq_bot_of_surjective_derivative
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (hsurj : Function.Surjective (mfderiv IN I iota x)) :
    h.normalSpaceAt x = ⊥ := by
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_bot]
    obtain ⟨u, hu⟩ := hsurj v
    have hvv := (h.mem_normalSpaceAt_iff x v).mp hv u
    rw [hu] at hvv
    by_contra hv0
    exact (gM.pos (iota x) v hv0).ne' hvv
  · intro hv
    rw [Submodule.mem_bot] at hv
    subst v
    exact Submodule.zero_mem _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_bot_of_surjective_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_bot_of_surjective_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_bot_of_surjective_derivative ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_bot_of_surjective_derivative

omit [FiniteDimensional ℝ E] in
theorem mfderiv_eq_zero_of_finrank_eq_zero
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (_h : IsRiemannianIsometricImmersion gN gM iota)
    (hdim : Module.finrank ℝ EN = 0) (x : N) :
    mfderiv IN I iota x = 0 := by
  let _ : Subsingleton EN := Module.finrank_zero_iff.mp hdim
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = 0 :=
    (tangentSpaceModelContinuousLinearEquiv (I := IN) x).injective
      (Subsingleton.elim _ _)
  rw [hu]
  exact ContinuousLinearMap.map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mfderiv_eq_zero_of_finrank_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mfderiv_eq_zero_of_finrank_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mfderiv_eq_zero_of_finrank_eq_zero ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.mfderiv_eq_zero_of_finrank_eq_zero

omit [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E] in
private def normalSpaceAtEquivTangentSpaceOfEqTop
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (htop : h.normalSpaceAt x = ⊤) :
    h.normalSpaceAt x ≃ TangentSpace I (iota x) where
  toFun v := v.1
  invFun v := ⟨v, by rw [htop]; exact Submodule.mem_top⟩
  left_inv v := Subtype.ext rfl
  right_inv _ := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAtEquivTangentSpaceOfEqTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAtEquivTangentSpaceOfEqTop target :: scope.openDecls } }

def normalBundleTotalSpaceEquivTangentSpaceAt
    [Subsingleton N]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota)
    (x0 : N) (hdim : Module.finrank ℝ EN = 0) :
    h.NormalBundleTotalSpace ≃ TangentSpace I (iota x0) := by
  letI : Unique N :=
    { default := x0
      uniq := fun x ↦ Subsingleton.elim x x0 }
  refine (Equiv.uniqueSigma (fun x ↦ h.normalSpaceAt x)).trans ?_
  apply normalSpaceAtEquivTangentSpaceOfEqTop h x0
  exact h.normalSpaceAt_eq_top_of_derivative_eq_zero x0
    (h.mfderiv_eq_zero_of_finrank_eq_zero hdim x0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleTotalSpaceEquivTangentSpaceAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleTotalSpaceEquivTangentSpaceAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleTotalSpaceEquivTangentSpaceAt ``Submission.DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleTotalSpaceEquivTangentSpaceAt

end IsRiemannianIsometricImmersion
end DifferentialGeometry.Geometry
