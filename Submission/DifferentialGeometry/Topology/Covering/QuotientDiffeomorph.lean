import Submission.DifferentialGeometry.Topology.Covering.DeckGroup
import Submission.DifferentialGeometry.Topology.Manifold.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff

variable {n : ℕ∞ω}
  {k : Type*} [NontriviallyNormedField k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace k F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners k E H} {J : ModelWithCorners k F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [T2Space M] [LocallyCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
  [IsCancelSMul G M] [ContMDiffConstSMul I n G M]

open _root_.IsQuotientCoveringMap in
noncomputable def IsQuotientCoveringMap.orbitRelQuotientDiffeomorph
    {p : M → N} (hp : IsQuotientCoveringMap p G)
    (hp' : IsLocalDiffeomorph I J n p) :
    MulAction.orbitRel.Quotient G M ≃ₘ^n⟮I, J⟯ N := by
  let e := hp.orbitRelQuotientHomeomorph
  let q : M → MulAction.orbitRel.Quotient G M := Quotient.mk''
  have hq := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (n := n) (G := G) (M := M) I
  have hcomp : (e : MulAction.orbitRel.Quotient G M → N) ∘ q = p := by
    funext x
    exact hp.orbitRelQuotientHomeomorph_apply x
  have hinv : (e.symm : N → MulAction.orbitRel.Quotient G M) ∘ p = q := by
    funext x
    apply e.injective
    change e (e.symm (p x)) = e (q x)
    rw [e.apply_symm_apply]
    exact (hp.orbitRelQuotientHomeomorph_apply x).symm
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := hq.contMDiff_of_comp_of_surjective
        (Quotient.mk_surjective) (by
          change ContMDiff I J n ((e : _ → N) ∘ q)
          rw [hcomp]
          exact hp'.contMDiff)
      contMDiff_invFun := hp'.contMDiff_of_comp_of_surjective hp.surjective
        (by
          change ContMDiff I I n ((e.symm : N → _) ∘ p)
          rw [hinv]
          exact hq.contMDiff) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsQuotientCoveringMap.orbitRelQuotientDiffeomorph then
    throwError "Refusing to shadow existing declaration IsQuotientCoveringMap.orbitRelQuotientDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `IsQuotientCoveringMap.orbitRelQuotientDiffeomorph ``Submission.IsQuotientCoveringMap.orbitRelQuotientDiffeomorph

open _root_.IsQuotientCoveringMap in
@[simp] theorem IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_apply
    {p : M → N} (hp : IsQuotientCoveringMap p G)
    (hp' : IsLocalDiffeomorph I J n p) (x : M) :
    hp.orbitRelQuotientDiffeomorph hp' (Quotient.mk'' x) = p x :=
  hp.orbitRelQuotientHomeomorph_apply x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_apply ``Submission.IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_apply

open _root_.IsQuotientCoveringMap in
@[simp] theorem IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_symm_apply
    {p : M → N} (hp : IsQuotientCoveringMap p G)
    (hp' : IsLocalDiffeomorph I J n p) (x : M) :
    (hp.orbitRelQuotientDiffeomorph hp').symm (p x) = Quotient.mk'' x := by
  apply (hp.orbitRelQuotientDiffeomorph hp').injective
  change (hp.orbitRelQuotientDiffeomorph hp')
    ((hp.orbitRelQuotientDiffeomorph hp').symm (p x)) =
      (hp.orbitRelQuotientDiffeomorph hp') (Quotient.mk'' x)
  rw [Diffeomorph.apply_symm_apply, hp.orbitRelQuotientDiffeomorph_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_symm_apply ``Submission.IsQuotientCoveringMap.orbitRelQuotientDiffeomorph_symm_apply
