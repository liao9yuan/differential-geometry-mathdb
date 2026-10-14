import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorus
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Submission.DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.IC target :: scope.openDecls } }

namespace SphereMappingTorusIsotopy

abbrev flatten (D : SphereMappingTorusIsotopy) : SphereMappingTorusIsotopy where
  target := D.target
  isotopy t := D.isotopy (Real.smoothTransition (3 * t - 1))
  continuous_apply := D.continuous_apply.comp
    (continuous_fst.prodMk (Real.smoothTransition.continuous.comp (by fun_prop)))
  isotopy_zero := by
    rw [Real.smoothTransition.zero_of_nonpos (by norm_num)]
    exact D.isotopy_zero
  isotopy_one := by
    rw [Real.smoothTransition.one_of_one_le (by norm_num)]
    exact D.isotopy_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten ``Submission.DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten

theorem flatten_lower (D : SphereMappingTorusIsotopy) {t : ℝ} (ht : t ≤ 1 / 3) :
    D.flatten.isotopy t = Diffeomorph.refl (𝓡 2) SphereTwo ∞ := by
  change D.isotopy (Real.smoothTransition (3 * t - 1)) = _
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  exact D.isotopy_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_lower ``Submission.DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_lower

theorem flatten_upper (D : SphereMappingTorusIsotopy) {t : ℝ} (ht : 2 / 3 ≤ t) :
    D.flatten.isotopy t = D.target := by
  change D.isotopy (Real.smoothTransition (3 * t - 1)) = _
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  exact D.isotopy_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_upper ``Submission.DifferentialGeometry.Topology.SphereMappingTorusIsotopy.flatten_upper

theorem contMDiff_flatten_apply (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1)) :
    ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.flatten.isotopy p.2 p.1) :=
  hD.comp (contMDiff_fst.prodMk
    (Real.smoothTransition.contDiff.contMDiff.comp
      (contMDiff_const.mul contMDiff_snd |>.sub contMDiff_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_apply ``Submission.DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_apply

theorem contMDiff_flatten_symm_apply (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.flatten.isotopy p.2).symm p.1) :=
  hD.comp (contMDiff_fst.prodMk
    (Real.smoothTransition.contDiff.contMDiff.comp
      (contMDiff_const.mul contMDiff_snd |>.sub contMDiff_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_symm_apply ``Submission.DifferentialGeometry.Topology.SphereMappingTorusIsotopy.contMDiff_flatten_symm_apply

end SphereMappingTorusIsotopy

def sphereMappingTorusSeamDomain : TopologicalSpace.Opens (SphereTwo × ℝ) :=
  ⟨univ ×ˢ _root_.Set.Ioo (-(1 / 4 : ℝ)) (1 / 4), isOpen_univ.prod isOpen_Ioo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusSeamDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusSeamDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusSeamDomain ``Submission.DifferentialGeometry.Topology.sphereMappingTorusSeamDomain

def sphereMappingTorusSeam
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (p : sphereMappingTorusSeamDomain) : SphereMappingTorus f :=
  if ht : 0 ≤ p.val.2 then
    Quotient.mk _ (p.val.1, ⟨p.val.2, ht, by linarith [p.property.2.2]⟩)
  else
    Quotient.mk _ (f.symm p.val.1,
      ⟨1 + p.val.2, by linarith [p.property.2.1], by linarith [not_le.mp ht]⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusSeam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusSeam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusSeam ``Submission.DifferentialGeometry.Topology.sphereMappingTorusSeam

theorem sphereMappingTorusHomeomorph_flatten_seam (D : SphereMappingTorusIsotopy)
    (p : sphereMappingTorusSeamDomain) :
    sphereMappingTorusHomeomorph D.flatten (sphereMappingTorusSeam D.target p) =
      (p.val.1, (p.val.2 : AddCircle (1 : ℝ))) := by
  unfold sphereMappingTorusSeam
  split_ifs with ht
  · change (D.flatten.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ))) = _
    rw [D.flatten_lower (by linarith [p.property.2.2])]
    rfl
  · change (D.flatten.isotopy (1 + p.val.2) (D.target.symm p.val.1),
      ((1 + p.val.2 : ℝ) : AddCircle (1 : ℝ))) = _
    rw [D.flatten_upper (by linarith [p.property.2.1]), D.target.apply_symm_apply]
    refine Prod.ext (by rfl) ?_
    simp only [AddCircle.coe_add, AddCircle.coe_period, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_flatten_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_flatten_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_flatten_seam ``Submission.DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_flatten_seam

private theorem isLocalDiffeomorph_sphere_prod_circle :
    IsLocalDiffeomorph IC IC ∞
      (fun p : SphereTwo × ℝ => (p.1, (p.2 : AddCircle (1 : ℝ)))) := by
  intro p
  obtain ⟨d, hp, hd⟩ := AddCircle.isLocalDiffeomorph_coe p.2
  let F : PartialDiffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × AddCircle (1 : ℝ)) ∞ :=
    { toPartialEquiv := (PartialEquiv.refl SphereTwo).prod d.toPartialEquiv
      open_source := isOpen_univ.prod d.open_source
      open_target := isOpen_univ.prod d.open_target
      contMDiffOn_toFun := contMDiff_fst.contMDiffOn.prodMk
        (d.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2))
      contMDiffOn_invFun := contMDiff_fst.contMDiffOn.prodMk
        (d.contMDiffOn_invFun.comp contMDiff_snd.contMDiffOn (fun _ h => h.2)) }
  refine ⟨F, ⟨mem_univ _, hp⟩, ?_⟩
  intro q hq
  exact Prod.ext rfl (hd hq.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.isLocalDiffeomorph_sphere_prod_circle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.isLocalDiffeomorph_sphere_prod_circle target :: scope.openDecls } }

@[instance_reducible]
def sphereMappingTorusChartedSpace (D : SphereMappingTorusIsotopy) :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (sphereMappingTorusHomeomorph D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusChartedSpace ``Submission.DifferentialGeometry.Topology.sphereMappingTorusChartedSpace

def sphereMappingTorusDiffeomorph (D : SphereMappingTorusIsotopy) :
    let _ := sphereMappingTorusChartedSpace D
    Diffeomorph IC IC (SphereMappingTorus D.target) (SphereTwo × AddCircle (1 : ℝ)) ∞ :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := IC) (n := ∞) (sphereMappingTorusHomeomorph D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusDiffeomorph ``Submission.DifferentialGeometry.Topology.sphereMappingTorusDiffeomorph

theorem sphereMappingTorusSeam_isLocalDiffeomorph (D : SphereMappingTorusIsotopy) :
    let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
      sphereMappingTorusChartedSpace D.flatten
    IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusSeam D.target) := by
  let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
      sphereMappingTorusChartedSpace D.flatten
  have hproj := DifferentialGeometry.isLocalDiffeomorph_restrict_open
    sphereMappingTorusSeamDomain
    (isLocalDiffeomorph_sphere_prod_circle.isLocalDiffeomorphOn sphereMappingTorusSeamDomain)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (sphereMappingTorusDiffeomorph D.flatten).symm.isLocalDiffeomorph hproj
  have heq : (sphereMappingTorusDiffeomorph D.flatten).symm ∘
      (fun p : sphereMappingTorusSeamDomain => (p.val.1, (p.val.2 : AddCircle (1 : ℝ)))) =
        sphereMappingTorusSeam D.target := by
    funext p
    apply (sphereMappingTorusHomeomorph D.flatten).injective
    change sphereMappingTorusHomeomorph D.flatten
      ((sphereMappingTorusHomeomorph D.flatten).symm _) = _
    rw [Homeomorph.apply_symm_apply, sphereMappingTorusHomeomorph_flatten_seam]
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusSeam_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusSeam_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusSeam_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.sphereMappingTorusSeam_isLocalDiffeomorph


namespace SphereMappingTorusIsotopy

def track (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (D.isotopy p.2 p.1, p.2)
  invFun p := ((D.isotopy p.2).symm p.1, p.2)
  left_inv p := Prod.ext ((D.isotopy p.2).symm_apply_apply p.1) rfl
  right_inv p := Prod.ext ((D.isotopy p.2).apply_symm_apply p.1) rfl
  contMDiff_toFun := hD.prodMk contMDiff_snd
  contMDiff_invFun := hDi.prodMk contMDiff_snd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.track then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereMappingTorusIsotopy.track"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereMappingTorusIsotopy.track ``Submission.DifferentialGeometry.Topology.SphereMappingTorusIsotopy.track

end SphereMappingTorusIsotopy

def sphereMappingTorusInteriorDomain : TopologicalSpace.Opens (SphereTwo × ℝ) :=
  ⟨univ ×ˢ _root_.Set.Ioo (0 : ℝ) 1, isOpen_univ.prod isOpen_Ioo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusInteriorDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusInteriorDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusInteriorDomain ``Submission.DifferentialGeometry.Topology.sphereMappingTorusInteriorDomain

def sphereMappingTorusInterior
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (p : sphereMappingTorusInteriorDomain) : SphereMappingTorus f :=
  Quotient.mk _ (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusInterior ``Submission.DifferentialGeometry.Topology.sphereMappingTorusInterior

theorem sphereMappingTorusHomeomorph_interior (D : SphereMappingTorusIsotopy)
    (p : sphereMappingTorusInteriorDomain) :
    sphereMappingTorusHomeomorph D (sphereMappingTorusInterior D.target p) =
      (D.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_interior ``Submission.DifferentialGeometry.Topology.sphereMappingTorusHomeomorph_interior

theorem sphereMappingTorusInterior_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D
    IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusInterior D.target) := by
  let _ := sphereMappingTorusChartedSpace D
  have hfull := DifferentialGeometry.isLocalDiffeomorph_comp
    isLocalDiffeomorph_sphere_prod_circle (D.track hD hDi).isLocalDiffeomorph
  have hres := DifferentialGeometry.isLocalDiffeomorph_restrict_open
    sphereMappingTorusInteriorDomain (hfull.isLocalDiffeomorphOn sphereMappingTorusInteriorDomain)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (sphereMappingTorusDiffeomorph D).symm.isLocalDiffeomorph hres
  have heq : (sphereMappingTorusDiffeomorph D).symm ∘
      (fun p : sphereMappingTorusInteriorDomain =>
        (D.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ)))) =
        sphereMappingTorusInterior D.target := by
    funext p
    apply (sphereMappingTorusHomeomorph D).injective
    change sphereMappingTorusHomeomorph D ((sphereMappingTorusHomeomorph D).symm _) = _
    rw [Homeomorph.apply_symm_apply, sphereMappingTorusHomeomorph_interior]
  change IsLocalDiffeomorph IC IC ∞ ((sphereMappingTorusDiffeomorph D).symm ∘
    (fun p : sphereMappingTorusInteriorDomain =>
      (D.isotopy p.val.2 p.val.1, (p.val.2 : AddCircle (1 : ℝ))))) at h
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorusInterior_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorusInterior_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorusInterior_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.sphereMappingTorusInterior_isLocalDiffeomorph

theorem sphereMappingTorus_interior_seam_cover
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) :
    range (sphereMappingTorusInterior f) ∪ _root_.Set.range (sphereMappingTorusSeam f) = univ := by
  apply _root_.Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
    by_cases hz : p.2.val = 0
    · right
      refine ⟨⟨(p.1, 0), _root_.Set.mem_univ _, by norm_num⟩, ?_⟩
      simp only [sphereMappingTorusSeam, le_refl, dite_true]
      congr 1
      exact Prod.ext rfl (Subtype.ext hz.symm)
    · by_cases ho : p.2.val = 1
      · right
        refine ⟨⟨(f p.1, 0), _root_.Set.mem_univ _, by norm_num⟩, ?_⟩
        simp only [sphereMappingTorusSeam, le_refl, dite_true]
        exact Quotient.sound (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨ho, rfl, rfl⟩))
      · left
        refine ⟨⟨(p.1, p.2.val), _root_.Set.mem_univ _,
          lt_of_le_of_ne p.2.property.1 (Ne.symm hz), lt_of_le_of_ne p.2.property.2 ho⟩, ?_⟩
        rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorus_interior_seam_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorus_interior_seam_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorus_interior_seam_cover ``Submission.DifferentialGeometry.Topology.sphereMappingTorus_interior_seam_cover

theorem sphereMappingTorus_flatten_smooth_charts (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
      sphereMappingTorusChartedSpace D.flatten
    IsManifold IC ∞ (SphereMappingTorus D.target) ∧
      IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusInterior D.target) ∧
      IsLocalDiffeomorph IC IC ∞ (sphereMappingTorusSeam D.target) := by
  let _ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (SphereMappingTorus D.target) :=
    sphereMappingTorusChartedSpace D.flatten
  refine ⟨?_, ?_, sphereMappingTorusSeam_isLocalDiffeomorph D⟩
  · exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
      (I := IC) (n := ∞) (sphereMappingTorusHomeomorph D.flatten)
  · exact sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
      (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereMappingTorus_flatten_smooth_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereMappingTorus_flatten_smooth_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereMappingTorus_flatten_smooth_charts ``Submission.DifferentialGeometry.Topology.sphereMappingTorus_flatten_smooth_charts

end DifferentialGeometry.Topology
