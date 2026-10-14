import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]

def clopenSumDiffeomorph (U : _root_.TopologicalSpace.Opens M) (hU : IsClosed (U : Set M)) :
    Diffeomorph I I (U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : _root_.TopologicalSpace.Opens M)) M ∞ := by
  classical
  let V : _root_.TopologicalSpace.Opens M := ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩
  let e : U ⊕ V ≃ M := Equiv.Set.sumCompl (U : Set M)
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact (contMDiff_subtype_val (U := U)).sumElim (contMDiff_subtype_val (U := V))
  · intro x
    by_cases hx : x ∈ U
    · have he : (fun y : U => e.symm y.val) = (Sum.inl : U → U ⊕ V) := by
        funext y
        exact Equiv.Set.sumCompl_symm_apply y
      have h : ContMDiffAt I I ∞ (fun y : U => e.symm y.val) ⟨x, hx⟩ := by
        rw [he]
        exact ContMDiff.inl.contMDiffAt
      exact (contMDiffAt_subtype_iff (I := I) (I' := I) (U := U) (f := e.symm) (x := ⟨x, hx⟩)).mp h
    · have he : (fun y : V => e.symm y.val) = (Sum.inr : V → U ⊕ V) := by
        funext y
        exact Equiv.Set.sumCompl_symm_apply_compl y
      have h : ContMDiffAt I I ∞ (fun y : V => e.symm y.val) ⟨x, hx⟩ := by
        rw [he]
        exact ContMDiff.inr.contMDiffAt
      exact (contMDiffAt_subtype_iff (I := I) (I' := I) (U := V) (f := e.symm) (x := ⟨x, hx⟩)).mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph

theorem clopenSumDiffeomorph_inl (U : _root_.TopologicalSpace.Opens M) (hU : IsClosed (U : Set M)) (p : U) :
    clopenSumDiffeomorph I U hU (Sum.inl p) = p.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inl ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inl

theorem clopenSumDiffeomorph_inr (U : _root_.TopologicalSpace.Opens M) (hU : IsClosed (U : Set M))
    (p : (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : _root_.TopologicalSpace.Opens M)) :
    clopenSumDiffeomorph I U hU (Sum.inr p) = p.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inr ``Submission.DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph_inr
end DifferentialGeometry.Topology.Manifold
