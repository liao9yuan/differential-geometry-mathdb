import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Manifold _root_.Set _root_.Topology
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
  [TopologicalSpace N] [ChartedSpace G N]

def partialDiffeomorphOfInjectiveLocalDiffeomorph (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    PartialDiffeomorph I J M N ∞ := by
  let hopen := hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj
  let e := hopen.toOpenPartialHomeomorph f
  refine {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hf.contMDiff.contMDiffOn
    contMDiffOn_invFun := ?_ }
  change ContMDiffOn J I ∞ e.symm e.target
  intro y hy
  have hyrange : y ∈ _root_.Set.range f := by
    simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_target] using hy
  obtain ⟨x, rfl⟩ := hyrange
  obtain ⟨Ψ, hx, hagree⟩ := hf x
  have htarget : f x ∈ Ψ.target := by
    rw [hagree hx]
    exact Ψ.toPartialEquiv.map_source hx
  have heq : (e.symm : N → M) =ᶠ[nhds (f x)] (Ψ.symm : N → M) := by
    filter_upwards [Ψ.open_target.mem_nhds htarget] with q hq
    have hright : f (Ψ.symm q) = q :=
      (hagree (Ψ.toPartialEquiv.map_target hq)).trans (Ψ.toPartialEquiv.right_inv hq)
    have hqrange : q ∈ _root_.Set.range f := ⟨Ψ.symm q, hright⟩
    apply hinj
    exact (hopen.toOpenPartialHomeomorph_right_inv f hqrange).trans hright.symm
  have hInv := Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds htarget)
  exact (hInv.congr_of_eventuallyEq heq).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph


@[simp] theorem partialDiffeomorphOfInjectiveLocalDiffeomorph_apply (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) (x : M) :
    partialDiffeomorphOfInjectiveLocalDiffeomorph f hf hinj x = f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_apply


@[simp] theorem partialDiffeomorphOfInjectiveLocalDiffeomorph_source (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    (partialDiffeomorphOfInjectiveLocalDiffeomorph f hf hinj).source = univ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_source


@[simp] theorem partialDiffeomorphOfInjectiveLocalDiffeomorph_target (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f) :
    (partialDiffeomorphOfInjectiveLocalDiffeomorph f hf hinj).target = _root_.Set.range f := by
  exact (hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj).toOpenPartialHomeomorph_target f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.partialDiffeomorphOfInjectiveLocalDiffeomorph_target

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
