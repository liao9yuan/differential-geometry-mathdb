import Submission.DifferentialGeometry.Topology.Homology.Local.LocalGoodUnion
import Submission.DifferentialGeometry.Topology.Homology.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.Metric

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

lemma isZero_of_forall_eq_zero {M : ModuleCat.{u} ℤ} (h : ∀ m : M, m = 0) : _root_.CategoryTheory.Limits.IsZero M :=
  ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_of_forall_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_of_forall_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_of_forall_eq_zero ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_of_forall_eq_zero

section support

variable {X : TopCat.{u}} {A B : Set X}

def inclSubSub (K : Set (TopCat.of A)) (hKB : Subtype.val '' K ⊆ B) :
    TopCat.of K ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x => ⟨x.1.1, hKB ⟨x.1, x.2, rfl⟩⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclSubSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclSubSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclSubSub ``Submission.DifferentialGeometry.Topology.SingularPair.inclSubSub

lemma inclSubSub_inclOfLE (K : Set (TopCat.of A)) (hKB : Subtype.val '' K ⊆ B) (hB : B ⊆ A) :
    inclSubSub K hKB ≫ inclOfLE hB = incl (TopCat.of A) K := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclSubSub_inclOfLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclSubSub_inclOfLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclSubSub_inclOfLE ``Submission.DifferentialGeometry.Topology.SingularPair.inclSubSub_inclOfLE

theorem exists_isCompact_subset_forall_mem_range (X : TopCat.{u}) (A : Set X) (k : ℕ)
    (c : singularHomology R (TopCat.of A) k) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ ∀ (B : Set X) (hB : B ⊆ A), K ⊆ B →
      c ∈ Set.range (singularHomologyMap R (inclOfLE hB) k) := by
  obtain ⟨K', hK', w, hw⟩ := exists_isCompact_mem_range_inclMap R (TopCat.of A) k c
  refine ⟨Subtype.val '' K', hK'.image continuous_subtype_val, Subtype.coe_image_subset A K',
    fun B hB hKB => ⟨singularHomologyMap R (inclSubSub K' hKB) k w, ?_⟩⟩
  rw [← ModuleCat.comp_apply, ← singularHomologyMap_comp, inclSubSub_inclOfLE]
  exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exists_isCompact_subset_forall_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exists_isCompact_subset_forall_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exists_isCompact_subset_forall_mem_range ``Submission.DifferentialGeometry.Topology.SingularPair.exists_isCompact_subset_forall_mem_range

end support

variable {n : ℕ}

theorem localGood.of_finset_convex (hn : 1 ≤ n) {ι : Type*} (F : Finset ι)
    (C : ι → Set (EU.{u} n)) (hC : ∀ a ∈ F, Convex ℝ (C a) ∧ IsCompact (C a)) :
    localGood R (TopCat.of (EU n)) n (⋃ a ∈ F, C a) := by
  classical
  induction F using Finset.induction_on generalizing C with
  | empty => exact (localGood.empty _ _).of_eq (by simp)
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert]
    refine localGood.union (hC a (Finset.mem_insert_self a F)).2.isClosed
      (isClosed_biUnion_finset fun b hb => (hC b (Finset.mem_insert_of_mem hb)).2.isClosed)
      (localGood.of_convex hn (hC a (Finset.mem_insert_self a F)).1
        (hC a (Finset.mem_insert_self a F)).2)
      (ih C fun b hb => hC b (Finset.mem_insert_of_mem hb)) ?_
    rw [Set.inter_iUnion₂]
    exact ih (fun b => C a ∩ C b) fun b hb =>
      ⟨(hC a (Finset.mem_insert_self a F)).1.inter (hC b (Finset.mem_insert_of_mem hb)).1,
        (hC a (Finset.mem_insert_self a F)).2.inter_right
          (hC b (Finset.mem_insert_of_mem hb)).2.isClosed⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_finset_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_finset_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_finset_convex ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_finset_convex

theorem localGood.of_finset_closedBall (hn : 1 ≤ n) (F : Finset (EU.{u} n)) (r : ℝ) :
    localGood R (TopCat.of (EU n)) n (⋃ a ∈ F, _root_.Metric.closedBall a r) :=
  localGood.of_finset_convex R hn F (fun a => _root_.Metric.closedBall a r) fun a _ =>
    ⟨convex_closedBall a r, _root_.ProperSpace.isCompact_closedBall a r⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_finset_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_finset_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_finset_closedBall ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_finset_closedBall

theorem exists_finset_closedBall_relativeHomologyMap_eq {A : Set (EU.{u} n)} (hA : IsCompact A) (j : ℕ)
    (α : relativeHomology R (TopCat.of (EU n)) Aᶜ (j + 1)) :
    ∃ (F : Finset (EU.{u} n)) (r : ℝ), 0 < r ∧ (∀ a ∈ F, a ∈ A) ∧
      ∃ (hsub : A ⊆ ⋃ a ∈ F, _root_.Metric.closedBall a r)
        (β : relativeHomology R (TopCat.of (EU n)) (⋃ a ∈ F, _root_.Metric.closedBall a r)ᶜ (j + 1)),
        relativeHomologyMap R (𝟙 (TopCat.of (EU n)))
          (mapsTo_id_of_subset (Set.compl_subset_compl.2 hsub)) (j + 1) β = α := by
  obtain ⟨Kz, hKz, hKzA, hrange⟩ :=
    exists_isCompact_subset_forall_mem_range R (TopCat.of (EU n)) Aᶜ j
      (δ R (TopCat.of (EU n)) Aᶜ j α)
  have hdisj : Disjoint A Kz := Set.disjoint_left.2 fun a ha haz => hKzA haz ha
  obtain ⟨r, hr, hdisj'⟩ := hdisj.exists_cthickenings hA hKz.isClosed
  obtain ⟨F, hFA, hAF⟩ :=
    hA.elim_nhds_subcover (fun a => _root_.Metric.ball a r) fun a _ => _root_.Metric.ball_mem_nhds a hr
  have hsub : A ⊆ ⋃ a ∈ F, _root_.Metric.closedBall a r :=
    hAF.trans (Set.iUnion₂_mono fun a _ => _root_.Metric.ball_subset_closedBall)
  refine ⟨F, r, hr, hFA, hsub, ?_⟩
  have hKKz : Kz ⊆ (⋃ a ∈ F, _root_.Metric.closedBall a r)ᶜ := by
    intro z hz hzK
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.1 hzK
    exact Set.disjoint_left.1 hdisj' (_root_.Metric.closedBall_subset_cthickening (hFA a ha) r hza)
      (_root_.Metric.self_subset_cthickening Kz hz)
  have hKA : (⋃ a ∈ F, _root_.Metric.closedBall a r)ᶜ ⊆ Aᶜ := Set.compl_subset_compl.2 hsub
  obtain ⟨γ, hγ⟩ := hrange _ hKA hKKz
  have hγ0 : inclMap R (TopCat.of (EU n)) (⋃ a ∈ F, _root_.Metric.closedBall a r)ᶜ j γ = 0 := by
    have h0 : δ R (TopCat.of (EU n)) Aᶜ j ≫ inclMap R (TopCat.of (EU n)) Aᶜ j = 0 :=
      (pair (TopCat.of (EU n)) Aᶜ).homologyδ_comp R (j + 1) j rfl
    rw [inclMap_eq_singularHomologyMap, ← inclOfLE_incl hKA, singularHomologyMap_comp, ModuleCat.comp_apply, hγ,
      ← inclMap_eq_singularHomologyMap, ← ModuleCat.comp_apply, h0]
    rfl
  obtain ⟨β, hβ⟩ :=
    (ShortComplex.moduleCat_exact_iff _).1 (les_exact₁ R (TopCat.of (EU n)) _ j) γ hγ0
  refine ⟨β, ?_⟩
  have hmono : _root_.CategoryTheory.Mono (δ R (TopCat.of (EU n)) Aᶜ j) :=
    (les_exact₃ R (TopCat.of (EU n)) Aᶜ j).mono_g_iff.2
      ((isZero_singularHomology_EU R n (j + 1) (by omega)).eq_zero_of_src _)
  apply (ModuleCat.mono_iff_injective _).1 hmono
  rw [← ModuleCat.comp_apply, ← δ_natural R (𝟙 (TopCat.of (EU n))) _ j, ModuleCat.comp_apply,
    hβ]
  have hrestr : restr (𝟙 (TopCat.of (EU n))) (mapsTo_id_of_subset hKA) = inclOfLE hKA := by
    ext x
    rfl
  rw [hrestr, hγ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exists_finset_closedBall_relativeHomologyMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exists_finset_closedBall_relativeHomologyMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exists_finset_closedBall_relativeHomologyMap_eq ``Submission.DifferentialGeometry.Topology.SingularPair.exists_finset_closedBall_relativeHomologyMap_eq

theorem localGood.of_isCompact_EU (hn : 1 ≤ n) {A : Set (EU.{u} n)} (hA : IsCompact A) :
    localGood R (TopCat.of (EU n)) n A := by
  refine ⟨fun i hi => ?_, fun α hα => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine isZero_of_forall_eq_zero fun α => ?_
    obtain ⟨F, r, hr, -, hsub, β, rfl⟩ := exists_finset_closedBall_relativeHomologyMap_eq R hA j α
    rw [eq_zero_of_isZero ((localGood.of_finset_closedBall R hn F r).isZero hi) β, map_zero]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    obtain ⟨F, r, hr, hF, hsub, β, rfl⟩ := exists_finset_closedBall_relativeHomologyMap_eq R hA j α
    have hβ : β = 0 := by
      refine (localGood.of_finset_closedBall R hn F r).eq_zero fun x hx => ?_
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 hx
      have hD : _root_.Metric.closedBall a r ⊆ ⋃ a ∈ F, _root_.Metric.closedBall a r :=
        Set.subset_iUnion₂ (s := fun a (_ : a ∈ F) => _root_.Metric.closedBall a r) a ha
      have hβD : relativeHomologyMap R (𝟙 (TopCat.of (EU (j + 1))))
          (mapsTo_id_of_subset (Set.compl_subset_compl.2 hD)) (j + 1) β = 0 := by
        have hiso := isIso_ptRes_of_convex R hn (convex_closedBall a r) (_root_.ProperSpace.isCompact_closedBall a r)
          (_root_.Metric.mem_closedBall_self hr.le) (j + 1)
        apply (ModuleCat.mono_iff_injective (relativeHomologyMap R (𝟙 (TopCat.of (EU (j + 1))))
          (compl_mapsTo (_root_.Metric.mem_closedBall_self hr.le)) (j + 1))).1 inferInstance
        have ha' : a ∈ _root_.Metric.closedBall a r := _root_.Metric.mem_closedBall_self hr.le
        rw [map_zero, relativeHomologyMap_id_apply_relativeHomologyMap_id_apply _ _ (compl_mapsTo (hD ha')),
          ← relativeHomologyMap_id_apply_relativeHomologyMap_id_apply
            (mapsTo_id_of_subset (Set.compl_subset_compl.2 hsub)) (compl_mapsTo (hF a ha))
            (compl_mapsTo (hD ha'))]
        exact hα a (hF a ha)
      rw [← relativeHomologyMap_id_apply_relativeHomologyMap_id_apply (mapsTo_id_of_subset (Set.compl_subset_compl.2 hD))
        (compl_mapsTo hxa) (compl_mapsTo hx), hβD, map_zero]
    rw [hβ, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.localGood.of_isCompact_EU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.localGood.of_isCompact_EU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.localGood.of_isCompact_EU ``Submission.DifferentialGeometry.Topology.SingularPair.localGood.of_isCompact_EU

end DifferentialGeometry.Topology.SingularPair

end
