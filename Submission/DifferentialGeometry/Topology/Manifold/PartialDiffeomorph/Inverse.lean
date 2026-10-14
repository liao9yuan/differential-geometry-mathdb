import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry

open _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff

universe u v uE uF uH uH'

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H' : Type uH'} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]
variable {n : WithTop ℕ∞}

namespace PartialDiffeomorph

theorem invFunOn_eqOn_symm
    [Nonempty M] (Ψ : PartialDiffeomorph I J M N n)
    {U : Set M} (hU : U ⊆ Ψ.source) :
    EqOn (Function.invFunOn (Ψ : M → N) U) (Ψ.symm : N → M) ((Ψ : M → N) '' U) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ((Ψ.toPartialEquiv.injOn.mono hU).leftInvOn_invFunOn hx).trans
    (Ψ.left_inv' (hU hx)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_symm ``Submission.DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_symm

theorem invFunOn_eventuallyEq_symm_on_image
    [Nonempty M] (Ψ : PartialDiffeomorph I J M N n)
    {U : _root_.TopologicalSpace.Opens M} (hU : (U : Set M) ⊆ Ψ.source) :
    ∀ y ∈ (Ψ : M → N) '' (U : Set M),
      Function.invFunOn (Ψ : M → N) (U : Set M) =ᶠ[nhds y] (Ψ.symm : N → M) := by
  intro y hy
  refine Filter.eventuallyEq_of_mem ((image_opens_isOpen Ψ hU).mem_nhds hy) ?_
  intro z hz
  exact invFunOn_eqOn_symm Ψ hU hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.invFunOn_eventuallyEq_symm_on_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.invFunOn_eventuallyEq_symm_on_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.invFunOn_eventuallyEq_symm_on_image ``Submission.DifferentialGeometry.PartialDiffeomorph.invFunOn_eventuallyEq_symm_on_image


theorem invFunOn_eqOn_of_eqOn
    [Nonempty M] (Φ : PartialDiffeomorph I J M N n)
    {U : Set M} (hU : U ⊆ Φ.source) {F : M → N}
    (hEq : _root_.Set.EqOn (Φ : M → N) F U) :
    EqOn (Function.invFunOn F U) (Φ.symm : N → M) (F '' U) := by
  have hF_inj : Set.InjOn F U := by
    intro x hx y hy hxy
    apply Φ.toPartialEquiv.injOn (hU hx) (hU hy)
    calc
      Φ x = F x := hEq hx
      _ = F y := hxy
      _ = Φ y := (hEq hy).symm
  rintro _ ⟨x, hx, rfl⟩
  calc
    Function.invFunOn F U (F x) = x := hF_inj.leftInvOn_invFunOn hx
    _ = Φ.symm (Φ x) := (Φ.left_inv' (hU hx)).symm
    _ = Φ.symm (F x) := congrArg Φ.symm (hEq hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_of_eqOn ``Submission.DifferentialGeometry.PartialDiffeomorph.invFunOn_eqOn_of_eqOn

end PartialDiffeomorph
end DifferentialGeometry
