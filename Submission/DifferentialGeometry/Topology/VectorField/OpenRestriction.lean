import Submission.DifferentialGeometry.Topology.VectorField.OpenSubtypePullback
import Submission.DifferentialGeometry.Topology.VectorField.Transport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
noncomputable section
namespace DifferentialGeometry.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

private theorem contMDiff_restrict
    (U : TopologicalSpace.Opens M) {V : ∀ x : M, TangentSpace I x}
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, V x.val⟩ : TangentBundle I U)) := by
  intro x
  let f := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U ⟨x⟩
  have h := contMDiffAt_mpullback_partialDiffeomorph f (by simp)
    (x := x) (by simp [f]) (hV.contMDiffAt (U.isOpen.mem_nhds x.property))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => congrArg
    (fun v : TangentSpace I y => (⟨y, v⟩ : TangentBundle I U))
    (DifferentialGeometry.Manifold.mpullback_openSubtype I U ⟨x⟩ V y).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.VectorField.contMDiff_restrict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.VectorField.contMDiff_restrict target :: scope.openDecls } }

theorem contMDiff_tangentSection_opens_iff
    (U : TopologicalSpace.Opens M) (W : ∀ x : U, TangentSpace I x) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, W x⟩ : TangentBundle I U)) ↔
      ContMDiff I I.tangent ∞ (fun x : U => (⟨x.val, W x⟩ : TangentBundle I M)) := by
  constructor
  · intro hW
    have hh := (contMDiff_subtype_val (I := I) (U := U) (n := ∞)).contMDiff_tangentMap (m := ∞) (by simp)
    have hgraph := hh.comp hW
    apply hgraph.congr
    intro x
    change (⟨x.val, W x⟩ : TangentBundle I M) =
      ⟨x.val, mfderiv I I (Subtype.val : U → M) x (W x)⟩
    rw [DifferentialGeometry.mfderiv_subtype_val]
    rfl
  · intro hW
    classical
    let V : ∀ x : M, TangentSpace I x := fun x => if hx : x ∈ U then W ⟨x, hx⟩ else 0
    have hVeq (x : U) : V x.val = W x := by
      exact dif_pos x.property
    have hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U := by
      have hh := hW.congr (fun x => congrArg
        (fun v : TangentSpace I x.val => (⟨x.val, v⟩ : TangentBundle I M)) (hVeq x))
      intro x hx
      exact ((contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp (hh ⟨x, hx⟩)).contMDiffWithinAt
    exact (contMDiff_restrict U hV).congr (fun x => congrArg
      (fun v : TangentSpace I x => (⟨x, v⟩ : TangentBundle I U)) (hVeq x).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.contMDiff_tangentSection_opens_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.contMDiff_tangentSection_opens_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.contMDiff_tangentSection_opens_iff ``Submission.DifferentialGeometry.VectorField.contMDiff_tangentSection_opens_iff

theorem contMDiff_tangentSection_restrict_opens_iff
    (U : TopologicalSpace.Opens M) (V : ∀ x : M, TangentSpace I x) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, V x.val⟩ : TangentBundle I U)) ↔
      ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U := by
  constructor
  · intro hV x hx
    have hh := (contMDiff_tangentSection_opens_iff U _).mp hV
    exact ((contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp (hh ⟨x, hx⟩)).contMDiffWithinAt
  · exact contMDiff_restrict U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens_iff ``Submission.DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens_iff

theorem contMDiff_tangentSection_restrict_opens
    (U : TopologicalSpace.Opens M) {V : ∀ x : M, TangentSpace I x}
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, V x.val⟩ : TangentBundle I U)) :=
  (contMDiff_tangentSection_restrict_opens_iff U V).mpr hV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens ``Submission.DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens

end DifferentialGeometry.VectorField
