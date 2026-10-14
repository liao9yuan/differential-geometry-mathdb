import Submission.DifferentialGeometry.Topology.Covering.EmbeddedLift
import Submission.DifferentialGeometry.Topology.Covering.FiniteFundamentalGroup
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u v

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N]

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem exists_disjoint_smooth_sphere_lifts
    {p : N → M} (hp : IsCoveringMap p) (hps : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (e : SphereTwo → M) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (z₀ : SphereTwo) :
    ∃ lifts : (p ⁻¹' {e z₀}) → SphereTwo → N,
      (∀ a, lifts a z₀ = a.val) ∧
      (∀ a, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (lifts a)) ∧
      (∀ a z, p (lifts a z) = e z) ∧
      Pairwise (fun a b => Disjoint (_root_.Set.range (lifts a)) (_root_.Set.range (lifts b))) ∧
      p ⁻¹' _root_.Set.range e = ⋃ a, _root_.Set.range (lifts a) := by
  have hex (a : p ⁻¹' {e z₀}) : ∃ f : C(SphereTwo, N), f z₀ = a.val ∧
      (∀ z, p (f z) = e z) ∧ ContMDiff (𝓡 2) (𝓡 3) ∞ f :=
    exists_smooth_lift_of_simplyConnected hp hps e he.contMDiff z₀ a.val a.property
  choose lifts hbase hproj hsmooth using hex
  have hemb (a : p ⁻¹' {e z₀}) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (lifts a) :=
    isSmoothEmbedding_of_lift_through_localDiffeomorph hps he (lifts a).continuous (hproj a)
  refine ⟨fun a => lifts a, hbase, hemb, hproj, ?_, ?_⟩
  · intro a b hab
    rw [Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨w, hw⟩
    have hzw : z = w := he.isEmbedding.injective
      ((hproj a z).symm.trans ((congrArg p (hz.trans hw.symm)).trans (hproj b w)))
    subst w
    have heq : (lifts a : SphereTwo → N) = lifts b := hp.eq_of_comp_eq
      (lifts a).continuous (lifts b).continuous (by funext z; exact (hproj a z).trans (hproj b z).symm)
      z (hz.trans hw.symm)
    apply hab
    apply Subtype.ext
    exact (hbase a).symm.trans ((congrFun heq z₀).trans (hbase b))
  · ext y
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨f, hfz, hpf, _hfs⟩ := exists_smooth_lift_of_simplyConnected hp hps e he.contMDiff z y hz.symm
      let a : p ⁻¹' {e z₀} := ⟨f z₀, hpf z₀⟩
      have heq : (lifts a : SphereTwo → N) = f := hp.eq_of_comp_eq
        (lifts a).continuous f.continuous (by funext w; exact (hproj a w).trans (hpf w).symm)
        z₀ (hbase a)
      exact mem_iUnion.mpr ⟨a, z, (congrFun heq z).trans hfz⟩
    · intro hy
      obtain ⟨a, z, rfl⟩ := mem_iUnion.mp hy
      exact ⟨z, (hproj a z).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_disjoint_smooth_sphere_lifts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_disjoint_smooth_sphere_lifts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_disjoint_smooth_sphere_lifts ``Submission.DifferentialGeometry.Topology.exists_disjoint_smooth_sphere_lifts

end DifferentialGeometry.Topology

end

end
