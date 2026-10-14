import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace Manifold
open _root_.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} {f : M → N} {x : M}

open _root_.Manifold in
private theorem isImmersionAtOfComplement_hasLeftInverse_mfderiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : _root_.Manifold.IsImmersionAtOfComplement F I J n f x) (hn : n ≠ 0) :
    (mfderiv I J f x).HasLeftInverse := by
  have hd : h.domChart.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn hn,
      (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn hn⟩
  have hde : (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) x).HasLeftInverse := by
    change (mfderiv I 𝓘(𝕜, E) (I ∘ h.domChart) x).HasLeftInverse
    rw [mfderiv_comp x I.mdifferentiableAt (hd.mdifferentiableAt h.mem_domChart_source),
      (I.hasMFDerivAt (x := h.domChart x)).mfderiv]
    change (mfderiv I I h.domChart x).HasLeftInverse
    exact (hd.mfderiv h.mem_domChart_source).hasLeftInverse
  let L : N → E := fun y => (h.equiv.symm ((h.codChart.extend J) y)).1
  have hA : ContDiff 𝕜 n (fun z : E' => (h.equiv.symm z).1) :=
    contDiff_fst.comp h.equiv.symm.contDiff
  have hLs : ContMDiffAt J 𝓘(𝕜, E) n L (f x) :=
    hA.contMDiff.contMDiffAt.comp (f x)
      (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas h.mem_codChart_source)
  have hL : MDifferentiableAt J 𝓘(𝕜, E) L (f x) := hLs.mdifferentiableAt hn
  have heq : L ∘ f =ᶠ[𝓝 x] (h.domChart.extend I) := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv hy'] at hw
    change (h.equiv.symm ((h.codChart.extend J) (f y))).1 = (h.domChart.extend I) y
    rw [hw, ContinuousLinearEquiv.symm_apply_apply]
  have hder := heq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, E))
  rw [mfderiv_comp x hL (h.contMDiffAt.mdifferentiableAt hn)] at hder
  exact (hde.congr hder).of_comp

run_cmd do
  let target := ``Submission.Manifold.isImmersionAtOfComplement_hasLeftInverse_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.isImmersionAtOfComplement_hasLeftInverse_mfderiv target :: scope.openDecls } }

open _root_.Manifold _root_.Manifold.IsImmersionAt in
theorem IsImmersionAt.hasLeftInverse_mfderiv
    (h : _root_.Manifold.IsImmersionAt I J n f x) (hn : n ≠ 0) :
    (mfderiv I J f x).HasLeftInverse :=
  isImmersionAtOfComplement_hasLeftInverse_mfderiv h.isImmersionAtOfComplement_complement hn

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Manifold.IsImmersionAt
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersionAt.hasLeftInverse_mfderiv then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersionAt.hasLeftInverse_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersionAt.hasLeftInverse_mfderiv ``Submission.Manifold.IsImmersionAt.hasLeftInverse_mfderiv

open _root_.Manifold _root_.Manifold.IsImmersionAt in
theorem IsImmersionAt.injective_mfderiv
    (h : _root_.Manifold.IsImmersionAt I J n f x) (hn : n ≠ 0) : Function.Injective (mfderiv I J f x) :=
  (h.hasLeftInverse_mfderiv hn).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersionAt.injective_mfderiv then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersionAt.injective_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersionAt.injective_mfderiv ``Submission.Manifold.IsImmersionAt.injective_mfderiv

end Manifold

namespace DifferentialGeometry.Topology.Manifold

open _root_.Function
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H' N]

theorem injective_mfderiv_of_isImmersionAt (f : M → N) (x : M)
    (hf : Manifold.IsImmersionAt I J ∞ f x) : _root_.Function.Injective (mfderiv I J f x) :=
  hf.injective_mfderiv (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt ``Submission.DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt

theorem bijective_mfderiv_of_isImmersionAt [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : M → N) (x : M) (hf : Manifold.IsImmersionAt I J ∞ f x)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : _root_.Function.Bijective (mfderiv I J f x) := by
  let D : E →L[ℝ] F := mfderiv I J f x
  exact D.toLinearMap.linearEquivOfInjective (injective_mfderiv_of_isImmersionAt I J f x hf) hdim |>.bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt ``Submission.DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
end DifferentialGeometry.Topology.Manifold
