import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalStarConvex
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeZero
import Mathlib.Tactic.Abel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem closedBall_complement_subset_point_complement {r : ℝ} (hr : 0 ≤ r) :
    (_root_.Metric.closedBall (0 : E) r)ᶜ ⊆ ({0}ᶜ : Set E) :=
  compl_subset_compl.mpr (singleton_subset_iff.mpr (_root_.Metric.mem_closedBall_self hr))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBall_complement_subset_point_complement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBall_complement_subset_point_complement target :: scope.openDecls } }

private def integralClosedBallToLocalHomologyIso (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    integralRelativeHomology n ((_root_.Metric.closedBall (0 : E) r)ᶜ) ≅ integralLocalHomology n (0 : E) :=
  integralBoundedStarConvexLocalHomologyIso n (_root_.Metric.mem_closedBall_self hr)
    ((convex_closedBall (0 : E) r).starConvex (_root_.Metric.mem_closedBall_self hr)) _root_.Metric.isBounded_closedBall

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralClosedBallToLocalHomologyIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralClosedBallToLocalHomologyIso target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E]

private theorem closedBall_shift_complement_mapsTo (c : E) (r : ℝ) :
    MapsTo (Homeomorph.subRight c) ((_root_.Metric.closedBall c r)ᶜ) ((_root_.Metric.closedBall (0 : E) r)ᶜ) := by
  intro x hx hball
  change x - c ∈ _root_.Metric.closedBall (0 : E) r at hball
  rw [mem_closedBall_zero_iff] at hball
  apply hx
  simpa only [_root_.Metric.mem_closedBall, dist_eq_norm] using hball

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBall_shift_complement_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBall_shift_complement_mapsTo target :: scope.openDecls } }

private theorem closedBall_shift_symm_complement_mapsTo (c : E) (r : ℝ) :
    MapsTo (Homeomorph.subRight c).symm ((_root_.Metric.closedBall (0 : E) r)ᶜ) ((_root_.Metric.closedBall c r)ᶜ) := by
  intro x hx hball
  change x + c ∈ _root_.Metric.closedBall c r at hball
  apply hx
  simpa only [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hball

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBall_shift_symm_complement_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBall_shift_symm_complement_mapsTo target :: scope.openDecls } }

private def integralClosedBallTranslateIso (n : ℕ) (c : E) (r : ℝ) :
    integralRelativeHomology n ((_root_.Metric.closedBall c r)ᶜ) ≅
      integralRelativeHomology n ((_root_.Metric.closedBall (0 : E) r)ᶜ) :=
  integralRelativeHomologyHomeomorphIso n (Homeomorph.subRight c)
    ((_root_.Metric.closedBall c r)ᶜ) ((_root_.Metric.closedBall (0 : E) r)ᶜ)
    (closedBall_shift_complement_mapsTo c r) (closedBall_shift_symm_complement_mapsTo c r)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralClosedBallTranslateIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralClosedBallTranslateIso target :: scope.openDecls } }

private def integralLocalTranslateToZeroIso (n : ℕ) (c : E) :
    integralLocalHomology n c ≅ integralLocalHomology n (0 : E) :=
  integralRelativeHomologyHomeomorphIso n (Homeomorph.subRight c) ({c}ᶜ) ({0}ᶜ)
    (fun _ hx => sub_ne_zero.mpr hx)
    (fun x hx h => hx (by
      change x + c = c at h
      exact add_right_cancel (h.trans (zero_add c).symm)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralLocalTranslateToZeroIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralLocalTranslateToZeroIso target :: scope.openDecls } }

variable [NormedSpace ℝ E]

def integralClosedBallLocalHomologyIso (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) :
    integralRelativeHomology n ((_root_.Metric.closedBall c r)ᶜ) ≅ integralLocalHomology n c :=
  integralClosedBallTranslateIso n c r ≪≫ integralClosedBallToLocalHomologyIso n r hr ≪≫
    (integralLocalTranslateToZeroIso n c).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso ``Submission.DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso

theorem integralClosedBallLocalHomologyIso_hom (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) :
    (integralClosedBallLocalHomologyIso n c r hr).hom.hom =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (show (_root_.Metric.closedBall c r)ᶜ ⊆ ({c}ᶜ : Set E) from
          fun _ hx h => hx (h.symm ▸ _root_.Metric.mem_closedBall_self hr)) := by
  let B := integralClosedBallTranslateIso (E := E) n c r
  let I := integralClosedBallToLocalHomologyIso (E := E) n r hr
  let L := integralLocalTranslateToZeroIso (E := E) n c
  have hcenter : _root_.Set.MapsTo (ContinuousMap.id E) ((_root_.Metric.closedBall c r)ᶜ) ({c}ᶜ : Set E) :=
    fun _ hx h => hx (h.symm ▸ _root_.Metric.mem_closedBall_self hr)
  have hB : _root_.Set.MapsTo (toContinuousMap (Homeomorph.subRight c))
      ((_root_.Metric.closedBall c r)ᶜ) ((_root_.Metric.closedBall (0 : E) r)ᶜ) := closedBall_shift_complement_mapsTo c r
  have hL : _root_.Set.MapsTo (toContinuousMap (Homeomorph.subRight c)) ({c}ᶜ : Set E) ({0}ᶜ : Set E) :=
    fun _ hx => sub_ne_zero.mpr hx
  have hI : _root_.Set.MapsTo (ContinuousMap.id E) ((_root_.Metric.closedBall (0 : E) r)ᶜ) ({0}ᶜ : Set E) :=
    closedBall_complement_subset_point_complement hr
  change (integralClosedBallLocalHomologyIso n c r hr).hom.hom =
    integralRelativeHomologyMap n (ContinuousMap.id E) hcenter
  have hcomm : I.hom.hom.comp B.hom.hom =
      L.hom.hom.comp (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter) := by
    change (integralRelativeHomologyMap n (ContinuousMap.id E) hI).comp
        (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight c)) hB) =
      (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.subRight c)) hL).comp
        (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter)
    rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    rfl
  apply LinearMap.ext
  intro a
  change L.inv.hom (I.hom.hom (B.hom.hom a)) = _
  have hpoint := LinearMap.congr_fun hcomm a
  change I.hom.hom (B.hom.hom a) =
    L.hom.hom (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter a) at hpoint
  rw [hpoint]
  exact congrArg (fun f => f.hom (integralRelativeHomologyMap n (ContinuousMap.id E) hcenter a))
    L.hom_inv_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso_hom ``Submission.DifferentialGeometry.Topology.integralClosedBallLocalHomologyIso_hom

private theorem closedBall_center_map_bijective (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) :
    Function.Bijective (integralRelativeHomologyMap n (ContinuousMap.id E)
      (show (_root_.Metric.closedBall c r)ᶜ ⊆ ({c}ᶜ : Set E) from
        fun _ hx h => hx (h.symm ▸ _root_.Metric.mem_closedBall_self hr))) := by
  rw [← integralClosedBallLocalHomologyIso_hom n c r hr]
  exact (integralClosedBallLocalHomologyIso n c r hr).toLinearEquiv.bijective

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBall_center_map_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBall_center_map_bijective target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric
open scoped _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem closedBall_complement_subset_point_complement_at
    {c y : E} {r : ℝ} (hy : y ∈ _root_.Metric.closedBall c r) :
    (_root_.Metric.closedBall c r)ᶜ ⊆ ({y}ᶜ : Set E) := by
  intro x hx h
  exact hx (h.symm ▸ hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBall_complement_subset_point_complement_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBall_complement_subset_point_complement_at target :: scope.openDecls } }

omit [NormedSpace ℝ E] in
private theorem point_complement_center_translation_mapsTo (c y : E) :
    MapsTo (Homeomorph.addRight (c - y)) ({y}ᶜ : Set E) ({c}ᶜ : Set E) := by
  intro x hx h
  apply hx
  apply (Homeomorph.addRight (c - y)).injective
  have hy : Homeomorph.addRight (c - y) y = c := by
    change y + (c - y) = c
    abel
  exact h.trans hy.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.point_complement_center_translation_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.point_complement_center_translation_mapsTo target :: scope.openDecls } }

omit [NormedSpace ℝ E] in
private theorem closedBall_center_translation_mapsTo
    {c y : E} {r : ℝ} (hy : y ∈ _root_.Metric.closedBall c r) :
    _root_.Set.MapsTo (toContinuousMap (Homeomorph.addRight (c - y)))
      ((_root_.Metric.closedBall c r)ᶜ) ({c}ᶜ : Set E) :=
  fun _ hx => point_complement_center_translation_mapsTo c y
    (closedBall_complement_subset_point_complement_at hy hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBall_center_translation_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBall_center_translation_mapsTo target :: scope.openDecls } }

private theorem closedBall_center_translation_homotopy_ne_center
    {c y : E} {r : ℝ} (hy : y ∈ _root_.Metric.closedBall c r)
    (t : unitInterval) (x : ((_root_.Metric.closedBall c r)ᶜ : Set E)) :
    x.val + t.val • (c - y) ≠ c := by
  have hx : r < ‖x.val - c‖ := by
    simpa only [_root_.Set.mem_compl_iff, _root_.Metric.mem_closedBall, dist_eq_norm, not_le] using x.property
  have ht : ‖t.val • (c - y)‖ ≤ ‖y - c‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1, norm_sub_rev c y]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg (y - c))
  intro heq
  have hxc : x.val - c = -(t.val • (c - y)) := by
    calc
      x.val - c = x.val - (x.val + t.val • (c - y)) :=
        congrArg (fun z : E => x.val - z) heq.symm
      _ = -(t.val • (c - y)) := by abel
  have hnorm : ‖x.val - c‖ ≤ r := by
    rw [hxc, norm_neg]
    exact ht.trans (by simpa only [_root_.Metric.mem_closedBall, dist_eq_norm] using hy)
  exact (not_le_of_gt hx) hnorm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBall_center_translation_homotopy_ne_center
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBall_center_translation_homotopy_ne_center target :: scope.openDecls } }

private def closedBallCenterTranslationHomotopy
    (c : E) (r : ℝ) (hr : 0 ≤ r) (y : E) (hy : y ∈ _root_.Metric.closedBall c r) :
    (singularPairRestriction (ContinuousMap.id E)
      (closedBall_complement_subset_point_complement_at (_root_.Metric.mem_closedBall_self hr))).Homotopy
      (singularPairRestriction (toContinuousMap (Homeomorph.addRight (c - y)))
        (closedBall_center_translation_mapsTo hy)) where
  toFun p := ⟨p.2.val + p.1.val • (c - y),
    closedBall_center_translation_homotopy_ne_center hy p.1 p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  map_zero_left x := by
    apply Subtype.ext
    simp [singularPairRestriction]
  map_one_left x := by
    apply Subtype.ext
    simp [singularPairRestriction]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.closedBallCenterTranslationHomotopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.closedBallCenterTranslationHomotopy target :: scope.openDecls } }

private theorem integralClosedBall_center_translation_map_eq
    (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) (y : E) (hy : y ∈ _root_.Metric.closedBall c r) :
    integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
        (closedBall_center_translation_mapsTo hy) =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (closedBall_complement_subset_point_complement_at (_root_.Metric.mem_closedBall_self hr)) := by
  cases n with
  | zero =>
    exact integralRelativeHomologyMap_zero_eq_of_joined _ _ _ _ _ _
      (fun x => ⟨PathConnectedSpace.somePath (x + (c - y)) x⟩)
  | succ n =>
    let := integralSingularHomology_subsingleton_of_contractible (n + 1) (Nat.succ_ne_zero n) E
    exact (integralRelativeHomologyMap_eq_of_restriction_homotopic n
      (ContinuousMap.id E) (toContinuousMap (Homeomorph.addRight (c - y)))
      ((_root_.Metric.closedBall c r)ᶜ) ({c}ᶜ : Set E) _ _
      ⟨closedBallCenterTranslationHomotopy c r hr y hy⟩).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralClosedBall_center_translation_map_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralClosedBall_center_translation_map_eq target :: scope.openDecls } }

theorem integralRelativeHomologyMap_closedBall_translation
    (n : ℕ) (c : E) (r : ℝ) (y : E) (hy : y ∈ _root_.Metric.closedBall c r) :
    (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
        (point_complement_center_translation_mapsTo c y)).comp
        (integralRelativeHomologyMap n (ContinuousMap.id E)
          (closedBall_complement_subset_point_complement_at hy)) =
      integralRelativeHomologyMap n (ContinuousMap.id E)
        (closedBall_complement_subset_point_complement_at
          (_root_.Metric.mem_closedBall_self (dist_nonneg.trans (mem_closedBall.mp hy)))) := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hy)
  have hT : _root_.Set.MapsTo (toContinuousMap (Homeomorph.addRight (c - y)))
      ({y}ᶜ : Set E) ({c}ᶜ : Set E) := point_complement_center_translation_mapsTo c y
  have hR : _root_.Set.MapsTo (ContinuousMap.id E) ((_root_.Metric.closedBall c r)ᶜ) ({y}ᶜ : Set E) :=
    closedBall_complement_subset_point_complement_at hy
  change (integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y))) hT).comp
    (integralRelativeHomologyMap n (ContinuousMap.id E) hR) = _
  rw [← integralRelativeHomologyMap_comp]
  exact integralClosedBall_center_translation_map_eq n c r hr y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_closedBall_translation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_closedBall_translation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_closedBall_translation ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_closedBall_translation

theorem existsUnique_closedBall_class_with_normalized_local_maps
    (n : ℕ) (c : E) (r : ℝ) (hr : 0 ≤ r) (ζ : integralLocalHomology n c) :
    ∃! a : integralRelativeHomology n ((_root_.Metric.closedBall c r)ᶜ),
      ∀ (y : E) (hy : y ∈ _root_.Metric.closedBall c r),
        integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
          (point_complement_center_translation_mapsTo c y)
          (integralRelativeHomologyMap n (ContinuousMap.id E)
            (closedBall_complement_subset_point_complement_at hy) a) = ζ := by
  let e := integralClosedBallLocalHomologyIso n c r hr
  have he : e.hom.hom = integralRelativeHomologyMap n (ContinuousMap.id E)
      (closedBall_complement_subset_point_complement_at (_root_.Metric.mem_closedBall_self hr)) :=
    integralClosedBallLocalHomologyIso_hom n c r hr
  have ha : ∀ (y : E) (hy : y ∈ _root_.Metric.closedBall c r),
      integralRelativeHomologyMap n (toContinuousMap (Homeomorph.addRight (c - y)))
        (point_complement_center_translation_mapsTo c y)
        (integralRelativeHomologyMap n (ContinuousMap.id E)
          (closedBall_complement_subset_point_complement_at hy) (e.inv.hom ζ)) = ζ := by
    intro y hy
    have h := LinearMap.congr_fun
      (integralRelativeHomologyMap_closedBall_translation n c r y hy) (e.inv.hom ζ)
    exact h.trans ((LinearMap.congr_fun he (e.inv.hom ζ)).symm.trans
      (congrArg (fun f => f.hom ζ) e.inv_hom_id))
  refine ⟨e.inv.hom ζ, ha, ?_⟩
  intro b hb
  have hmapcenter : (toContinuousMap (Homeomorph.addRight (c - c)) : C(E, E)) =
      ContinuousMap.id E := by
    ext x
    simp
  have hba := hb c (_root_.Metric.mem_closedBall_self hr)
  have haa := ha c (_root_.Metric.mem_closedBall_self hr)
  simp only [hmapcenter, integralRelativeHomologyMap_id, LinearMap.id_apply] at hba haa
  exact (closedBall_center_map_bijective (E := E) n c r hr).injective (hba.trans haa.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.existsUnique_closedBall_class_with_normalized_local_maps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.existsUnique_closedBall_class_with_normalized_local_maps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.existsUnique_closedBall_class_with_normalized_local_maps ``Submission.DifferentialGeometry.Topology.existsUnique_closedBall_class_with_normalized_local_maps

end DifferentialGeometry.Topology

end
