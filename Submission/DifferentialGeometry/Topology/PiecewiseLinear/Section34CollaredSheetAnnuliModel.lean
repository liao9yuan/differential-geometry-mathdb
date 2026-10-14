import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCellCoordinates
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingRibbonAnnuli
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusReversal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.isPLAnnulusWithEnds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set E} {X : Set (EuclideanSpace ℝ (Fin 3))}
    {ρ : E × ℝ → EuclideanSpace ℝ (Fin 3)} (hJ : IsPLSphere 1 J)
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ _root_.Set.Icc (0 : ℝ) 1) X) :
    IsPLAnnulusWithEnds X (ρ '' (J ×ˢ {0})) (ρ '' (J ×ˢ {1})) := by
  let J₀ := ρ '' (J ×ˢ {0})
  let η := fun x : E => ρ (x, 0)
  have hη : IsPLHomeomorphOn η J J₀ :=
    (hJ.isPolyhedron.isPLHomeomorphOn_prod_const 0).trans
      (hρ.restrict (hJ.isPolyhedron.prod (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
        (_root_.Set.prod_mono_right (singleton_subset_iff.mpr (by norm_num))))
  let ψ := ρ ∘ Prod.map (Function.invFunOn η J) id
  have hψ : IsPLHomeomorphOn ψ (J₀ ×ˢ _root_.Set.Icc (0 : ℝ) 1) X :=
    (hη.symm.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hρ
  refine ⟨J₀, ψ, hJ.of_isPLHomeomorphOn hη, hψ, ?_, ?_⟩
  · change J₀ = (ρ ∘ Prod.map (Function.invFunOn η J) id) '' (J₀ ×ˢ {0})
    rw [_root_.Set.image_comp, _root_.Set.prodMap_image_prod, hη.symm.image_eq, _root_.Set.image_id]
  · change ρ '' (J ×ˢ {1}) = (ρ ∘ Prod.map (Function.invFunOn η J) id) '' (J₀ ×ˢ {1})
    rw [_root_.Set.image_comp, _root_.Set.prodMap_image_prod, hη.symm.image_eq, _root_.Set.image_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLAnnulusWithEnds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLAnnulusWithEnds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLAnnulusWithEnds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPLAnnulusWithEnds

theorem IsPLAnnulusWithEnds.union_two_rim_annuli
    {X Y₀ Y₁ J₀ J₁ K₀ K₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsPLAnnulusWithEnds X J₀ J₁)
    (hY₀ : IsPLAnnulusWithEnds Y₀ J₀ K₀) (hY₁ : IsPLAnnulusWithEnds Y₁ J₁ K₁)
    (hXY₀ : X ∩ Y₀ = J₀) (hXY₁ : X ∩ Y₁ = J₁) (hdis : Disjoint Y₀ Y₁) :
    IsPLAnnulusWithEnds (X ∪ (Y₀ ∪ Y₁)) K₀ K₁ := by
  have hfirst := hY₀.symm.union hX (_root_.Set.inter_comm _ _ ▸ hXY₀)
  have hsecond : (Y₀ ∪ X) ∩ Y₁ = J₁ := by
    rw [_root_.Set.union_inter_distrib_right, hdis.inter_eq, _root_.Set.empty_union, hXY₁]
  have hall := hfirst.union hY₁ hsecond
  simpa only [_root_.Set.union_assoc, _root_.Set.union_comm Y₀ X, _root_.Set.union_left_comm Y₀ X Y₁] using hall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_rim_annuli then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_rim_annuli"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_rim_annuli ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_rim_annuli

theorem IsCylindricalDiagram.isPLAnnulusWithEnds_base_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} {P B : Set E}
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsCylindricalDiagram f P C)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) B) (hBP : B ⊆ P) :
    IsPLAnnulusWithEnds (f '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1))
      (f '' ({γ 0} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (f '' ({γ 1} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨ρ, hρ, hzero, hone⟩ := hf.exists_annulus_chart_of_base_arc hends hγ hBP
  simpa only [hzero, hone] using hρ.isPLAnnulusWithEnds
    ⟨id, isPolyhedron_stdSimplexBoundary_two.isPLHomeomorphOn_id⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_base_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_base_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_base_arc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_base_arc

theorem IsCylindricalDiagram.isPLAnnulusWithEnds_radial_band
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} {P : Set E}
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsCylindricalDiagram f P C)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {v : E} (hv : v ≠ 0)
    {d : ℝ} (hd : 0 < d) (hBP : (fun r : ℝ => r • v) '' _root_.Set.Icc 0 d ⊆ P) :
    IsPLAnnulusWithEnds (f '' (((fun r : ℝ => r • v) '' _root_.Set.Icc 0 d) ×ˢ _root_.Set.Icc (0 : ℝ) 1))
      (f '' ({0} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) (f '' ({d • v} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  have hδ : IsPLHomeomorphOn (fun r : ℝ => r • v) (_root_.Set.Icc 0 d)
      ((fun r : ℝ => r • v) '' _root_.Set.Icc 0 d) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v).toAffineMap isHPolytope_Icc)
      (smul_left_injective ℝ hv).injOn.bijOn_image
  have hγ := (isPLHomeomorphOn_mul_add_Icc hd
    (show d * 0 + 0 = 0 by ring) (show d * 1 + 0 = d by ring)).trans hδ
  simpa only [Function.comp_apply, _root_.MulZeroClass.mul_zero, zero_add, zero_smul, mul_one, add_zero] using
    hf.isPLAnnulusWithEnds_base_arc hends hγ hBP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_radial_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_radial_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_radial_band ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLAnnulusWithEnds_radial_band

theorem IsPLAnnulusWithEnds.rims_subset {X J₀ J₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsPLAnnulusWithEnds X J₀ J₁) : J₀ ⊆ X ∧ J₁ ⊆ X := by
  obtain ⟨J, ρ, -, hρ, rfl, rfl⟩ := hX
  exact ⟨(_root_.Set.image_mono (_root_.Set.prod_mono_right (singleton_subset_iff.mpr (by norm_num)))).trans
    hρ.image_eq.subset,
    (_root_.Set.image_mono (_root_.Set.prod_mono_right (singleton_subset_iff.mpr (by norm_num)))).trans
      hρ.image_eq.subset⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.rims_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.rims_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.rims_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.rims_subset

theorem IsPLAnnulusWithEnds.union_two_external_annuli
    {X R Y₀ Y₁ J₀ J₁ K₀ K₁ : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : IsPLAnnulusWithEnds X J₀ J₁) (hXR : X ⊆ R)
    (hY₀ : IsPLAnnulusWithEnds Y₀ J₀ K₀) (hY₁ : IsPLAnnulusWithEnds Y₁ J₁ K₁)
    (hY₀R : Y₀ ∩ R = J₀) (hY₁R : Y₁ ∩ R = J₁) (hdis : Disjoint Y₀ Y₁) :
    IsPLAnnulusWithEnds (X ∪ (Y₀ ∪ Y₁)) K₀ K₁ := by
  have h₀ : X ∩ Y₀ = J₀ := Subset.antisymm
    (fun _ h => hY₀R.subset ⟨h.2, hXR h.1⟩)
    (fun _ h => ⟨hX.rims_subset.1 h, (hY₀R.symm.subset h).1⟩)
  have h₁ : X ∩ Y₁ = J₁ := Subset.antisymm
    (fun _ h => hY₁R.subset ⟨h.2, hXR h.1⟩)
    (fun _ h => ⟨hX.rims_subset.2 h, (hY₁R.symm.subset h).1⟩)
  exact hX.union_two_rim_annuli hY₀ hY₁ h₀ h₁ hdis

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_external_annuli then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_external_annuli"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_external_annuli ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.union_two_external_annuli

end DifferentialGeometry.Topology.PiecewiseLinear
