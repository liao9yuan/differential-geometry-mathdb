import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Function _root_.Metric _root_.Set
open scoped _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem sphere_compl_two_points_isPreconnected
    (hn : 1 < n) (p q : _root_.Metric.sphere (0 : E) 1) (hpq : p ≠ q) :
    IsPreconnected {x : _root_.Metric.sphere (0 : E) 1 | x ≠ p ∧ x ≠ q} := by
  classical
  let U : Set (_root_.Metric.sphere (0 : E) 1) := {x | x ≠ p ∧ x ≠ q}
  let e := stereographic' n p
  let a : EuclideanSpace ℝ (Fin n) := e q
  have hq_source : q ∈ e.source := by
    simpa only [e, stereographic'_source, _root_.Set.mem_compl_iff,
      _root_.Set.mem_singleton_iff] using hpq.symm
  have hU_source : U ⊆ e.source := by
    intro x hx
    simpa only [e, stereographic'_source, _root_.Set.mem_compl_iff,
      _root_.Set.mem_singleton_iff] using hx.1
  have himage :
      e '' U = ({a}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      simp only [_root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, a]
      intro heq
      exact hx.2 (e.injOn (hU_source hx) hq_source heq)
    · intro y hy
      have hy_target : y ∈ e.target := by
        simp only [e, stereographic'_target, _root_.Set.mem_univ]
      let x : _root_.Metric.sphere (0 : E) 1 := e.symm y
      have hx_source : x ∈ e.source := e.map_target hy_target
      have hxp : x ≠ p := by
        simpa only [e, stereographic'_source, _root_.Set.mem_compl_iff,
          _root_.Set.mem_singleton_iff, x] using hx_source
      have hexy : e x = y := e.right_inv hy_target
      have hxq : x ≠ q := by
        intro hxq
        have hya : y ≠ a := by
          simpa only [_root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff] using hy
        apply hya
        calc
          y = e x := hexy.symm
          _ = e q := congrArg e hxq
          _ = a := rfl
      exact ⟨x, ⟨hxp, hxq⟩, hexy⟩
  let h : U ≃ₜ ({a}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    e.homeomorphOfImageSubsetSource hU_source himage
  have hrank :
      1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    simpa only [finrank_euclideanSpace_fin] using hn
  have htarget :
      IsPreconnected ({a}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank a).isConnected.isPreconnected
  let : PreconnectedSpace ({a}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    Subtype.preconnectedSpace htarget
  have hsource : PreconnectedSpace U :=
    h.symm.surjective.denseRange.preconnectedSpace h.symm.continuous
  exact isPreconnected_iff_preconnectedSpace.mpr hsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphere_compl_two_points_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphere_compl_two_points_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphere_compl_two_points_isPreconnected ``Submission.DifferentialGeometry.Geometry.sphere_compl_two_points_isPreconnected

end Geometry
end DifferentialGeometry
