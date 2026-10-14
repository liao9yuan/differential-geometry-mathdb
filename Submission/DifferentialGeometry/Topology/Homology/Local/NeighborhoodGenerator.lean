import Submission.DifferentialGeometry.Topology.Homology.Local.Translation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric
namespace DifferentialGeometry.Homology
variable {n : ℕ} (p : EuclideanSpace ℝ (Fin n))
  (U : Set (EuclideanSpace ℝ (Fin n))) (hp : p ∈ U) (hU : IsOpen U)
  [ContractibleSpace U] {k : Type} [Ring k] (A : ModuleCat k)

theorem puncturedNeighborhoodHomologyIso_translation_sphere (q : ℕ) :
    (puncturedNeighborhoodHomologyIso (TopCat.of (EuclideanSpace ℝ (Fin n)))
      U p hp A hU (q + 1)).hom ≫
      (localTranslationHomologyIso _ p A (q + 1)).hom ≫
      (localEuclideanSphereHomologyIso A n q).hom =
    (relativeReducedConnectingIso (TopCat.of U) ({(⟨p,hp⟩ : U)}ᶜ : Set U) A q).hom ≫
      (puncturedNeighborhoodSphereHomologyIso _ p U hp hU A q).hom := by
  let j : TopCat.of U ⟶ TopCat.of (EuclideanSpace ℝ (Fin n)) :=
    TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(U,EuclideanSpace ℝ (Fin n)))
  let t : TopCat.of (EuclideanSpace ℝ (Fin n)) ⟶ TopCat.of (EuclideanSpace ℝ (Fin n)) :=
    TopCat.ofHom (⟨fun y => y-p,continuous_id.sub continuous_const⟩ :
      C(EuclideanSpace ℝ (Fin n),EuclideanSpace ℝ (Fin n)))
  have ht : _root_.Set.MapsTo t ({p}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := fun _ hy => sub_ne_zero.mpr hy
  have hj := puncturedNeighborhood_mapsTo (TopCat.of (EuclideanSpace ℝ (Fin n))) U p hp
  have hm : (puncturedNeighborhoodHomologyIso (TopCat.of (EuclideanSpace ℝ (Fin n)))
      U p hp A hU (q + 1)).hom ≫ (localTranslationHomologyIso _ p A (q + 1)).hom =
      relativeHomologyMap A (j ≫ t) (ht.comp hj) (q + 1) :=
    (relativeHomologyMap_comp A j hj t ht (q + 1)).symm
  rw [← Category.assoc,hm]
  have hn := relativeReducedConnectingIso_naturality A (j ≫ t) (ht.comp hj) q
  have hs : TopCat.ofHom (puncturedNeighborhoodRadialMap _ p U hp) =
      relativeSubspaceMap (j ≫ t) (ht.comp hj) ≫
        TopCat.ofHom (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace ℝ (Fin n))).toFun := by
    rfl
  rw [puncturedNeighborhoodSphereHomologyIso_hom,hs,reducedSingularHomologyMap_comp]
  change _ ≫ ((relativeReducedConnectingIso (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) A q).hom ≫
      reducedSingularHomologyMap A
        (TopCat.ofHom (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace ℝ (Fin n))).toFun) q) = _
  rw [← Category.assoc,← hn,Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_translation_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_translation_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_translation_sphere ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodHomologyIso_translation_sphere

variable {d : ℕ}

theorem euclideanBallLocalGenerator_inclusion
    (x : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) (hr : 0 < r) :
    (puncturedNeighborhoodHomologyIso (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      (_root_.Metric.ball x r) x (_root_.Metric.mem_ball_self hr) (ModuleCat.of ℤ ℤ) _root_.Metric.isOpen_ball (d + 1)).hom
      (euclideanBallLocalGenerator x r hr) = euclideanLocalGeneratorAt x := by
  let _ : ContractibleSpace (_root_.Metric.ball x r) := (convex_ball x r).contractibleSpace ⟨x,_root_.Metric.mem_ball_self hr⟩
  apply (ModuleCat.mono_iff_injective
    ((localTranslationHomologyIso _ x (ModuleCat.of ℤ ℤ) (d + 1)).hom ≫
      (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom)).mp inferInstance
  have he := congrArg (fun f => f (euclideanBallLocalGenerator x r hr))
    (puncturedNeighborhoodHomologyIso_translation_sphere x (_root_.Metric.ball x r) (_root_.Metric.mem_ball_self hr)
      _root_.Metric.isOpen_ball (ModuleCat.of ℤ ℤ) d)
  have hs := congrArg (fun f => f (DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator d))
    (localBallSphereHomologyIso _ x r hr (ModuleCat.of ℤ ℤ) d).inv_hom_id
  have ht := congrArg (fun f => f (DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator d))
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id
  change _ = (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
    ((localTranslationHomologyIso _ x (ModuleCat.of ℤ ℤ) (d + 1)).hom (euclideanLocalGeneratorAt x))
  rw [euclideanLocalGeneratorAt_translate]
  exact he.trans (hs.trans ht.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanBallLocalGenerator_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanBallLocalGenerator_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanBallLocalGenerator_inclusion ``Submission.DifferentialGeometry.Homology.euclideanBallLocalGenerator_inclusion

end DifferentialGeometry.Homology
