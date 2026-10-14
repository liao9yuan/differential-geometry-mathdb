import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import Submission.DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mpullback_openSubtype_symm (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (V : ∀ x : U, TangentSpace I x) {x : M} (hx : x ∈ U) :
    _root_.VectorField.mpullback I I (openSubtypePartialDiffeomorph I U hU).symm V x =
      V ⟨x, hx⟩ := by
  let f := openSubtypePartialDiffeomorph I U hU
  have hxf : x ∈ f.symm.source := by simpa [f] using hx
  change (mfderiv I I f.symm x).inverse (V (f.symm x)) = V ⟨x, hx⟩
  rw [DifferentialGeometry.VectorField.inverse_mfderiv_partialDiffeomorph f.symm (by simp) hxf]
  have hi : mfderiv I I f.symm.symm (f.symm x) = ContinuousLinearMap.id ℝ E :=
    DifferentialGeometry.mfderiv_subtype_val U (f.symm x)
  rw [hi]
  change V (f.symm x) = V ⟨x, hx⟩
  rw [openSubtypePartialDiffeomorph_symm_apply I U hU hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.mpullback_openSubtype_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.mpullback_openSubtype_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.mpullback_openSubtype_symm ``Submission.DifferentialGeometry.Manifold.mpullback_openSubtype_symm

theorem mpullback_openSubtype (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (V : ∀ x : M, TangentSpace I x) (x : U) :
    _root_.VectorField.mpullback I I (openSubtypePartialDiffeomorph I U hU) V x =
      V x.val := by
  change (mfderiv I I (Subtype.val : U → M) x).inverse (V x.val) = V x.val
  rw [DifferentialGeometry.mfderiv_subtype_val]
  change (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap.inverse (V x.val) = V x.val
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.mpullback_openSubtype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.mpullback_openSubtype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.mpullback_openSubtype ``Submission.DifferentialGeometry.Manifold.mpullback_openSubtype

end DifferentialGeometry.Manifold
