import Submission.DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.ChartJacobianClmSmoothness
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.ContDiff

namespace DifferentialGeometry
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
private lemma tangent_baseSet_eq (α : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.tangent_baseSet_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.tangent_baseSet_eq target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma tangent_symmL_self_eq_one (α : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ α = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.tangent_symmL_self_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.tangent_symmL_self_eq_one target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma tangent_clmAt_self_eq_one (α : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.tangent_clmAt_self_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.tangent_clmAt_self_eq_one target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma contMDiffOn_coordChangeL_tangent (α β : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have h := contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _))
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α)
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) β)
  rw [tangent_baseSet_eq, tangent_baseSet_eq] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.contMDiffOn_coordChangeL_tangent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.contMDiffOn_coordChangeL_tangent target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma coordChangeL_apply_eq_clmAt_symmL
    (α β : M) {b : M}
    (hbα : b ∈ (chartAt H α).source) (hbβ : b ∈ (chartAt H β).source) (v : E) :
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E) v =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v) := by
  have hbα' : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    rw [tangent_baseSet_eq]; exact hbα
  have hbβ' : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) β).baseSet := by
    rw [tangent_baseSet_eq]; exact hbβ
  change ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) β) b) v =
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b v)
  rw [Trivialization.coordChangeL_apply _ _ ⟨hbα', hbβ'⟩]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hbβ',
      Bundle.Trivialization.symmL_apply _ hbα']

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.coordChangeL_apply_eq_clmAt_symmL
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.coordChangeL_apply_eq_clmAt_symmL target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffOn
    (α β : M) (φ : E →L[ℝ] ℝ) (w : E) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b w)))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have hcoord := contMDiffOn_coordChangeL_tangent (I := I) α β
  have hcoord_app : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E) w)
      ((chartAt H α).source ∩ (chartAt H β).source) :=
    hcoord.clm_apply contMDiffOn_const
  have hcoordj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ := φ.contMDiff
  have hwrapped : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        (((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E) w))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    intro b hb
    exact (hcoordj _).contMDiffWithinAt.comp _ (hcoord_app _ hb) (_root_.Set.mapsTo_univ _ _)
  refine hwrapped.congr ?_
  intro b ⟨hbα, hbβ⟩
  exact (congrArg φ
    (coordChangeL_apply_eq_clmAt_symmL (I := I) α β hbα hbβ w)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn ``Submission.DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffOn_swap
    (α β : M) (φ : E →L[ℝ] ℝ) (w : E) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) β).symmL ℝ b w)))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have h := tangentCoordChangeL_entry_contMDiffOn (I := I) β α φ w
  rw [Set.inter_comm] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn_swap ``Submission.DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffOn_swap

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffAt
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b w)))
      b₀ := by
  have hwrapped := tangentCoordChangeL_entry_contMDiffOn (I := I) α b₀ φ w
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt ``Submission.DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_eq_symmL_entry_self
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    (b₀ : M) :
    φ
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b₀
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b₀ w)) =
    φ
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b₀ w) := by
  have h := tangent_clmAt_self_eq_one (I := I) b₀
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_symmL_entry_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_symmL_entry_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_symmL_entry_self ``Submission.DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_symmL_entry_self

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffAt_swap
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b w)))
      b₀ := by
  have hwrapped := tangentCoordChangeL_entry_contMDiffOn_swap (I := I) α b₀ φ w
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt_swap ``Submission.DifferentialGeometry.Tensor.tangentCoordChangeL_entry_contMDiffAt_swap

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_eq_continuousLinearMapAt_entry_self
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    (b₀ : M) :
    φ
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b₀ w)) =
    φ
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀ w) := by
  have h := tangent_symmL_self_eq_one (I := I) b₀
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_continuousLinearMapAt_entry_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_continuousLinearMapAt_entry_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_continuousLinearMapAt_entry_self ``Submission.DifferentialGeometry.Tensor.tangentCoordChangeL_entry_eq_continuousLinearMapAt_entry_self

end Tensor
end DifferentialGeometry

end
