import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedGeometricCell
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricInclusion
import Submission.DifferentialGeometry.Topology.SimplicialComplex.FiniteFaceInduction
import Submission.DifferentialGeometry.Topology.SimplicialComplex.EmptyRealization
import Submission.DifferentialGeometry.Topology.SimplicialSet.Compactness
import Submission.DifferentialGeometry.Topology.Category.TopCat.PushoutInjectivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Simplicial
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

theorem geometricRealizationMap_injective (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Function.Injective (geometricRealizationMap K) := by
  apply finite_geometricFace_induction
    (fun L : Geometry.SimplicialComplex ℝ E => Function.Injective (geometricRealizationMap L)) ?_ ?_ K
  · intro L hL
    let : IsEmpty (SSet.toTop.obj (orderedSimplicialSet L.toPreAbstractSimplicialComplex)) :=
      isEmpty_orderedRealization _ hL
    exact Function.injective_of_subsingleton _
  · intro L _ s hs hOld
    let n := s.card - 1
    have hn : s.card = n + 1 :=
      (Nat.sub_add_cancel (Finset.card_pos.mpr (L.nonempty_of_mem_faces hs.1))).symm
    have hmax : IsMax (⟨s, hs.1⟩ : L.faces) := by
      intro t ht
      exact (hs.2 t.prop ht).symm.le
    have hP := (orderedFaceAttachment_isPushout L.toPreAbstractSimplicialComplex s hs.1 hn hmax).map
      SSet.toTop
    apply DifferentialGeometry.TopCat.Pushout.injective_of_cell_overlap hP (geometricRealizationMap L)
    · intro x y hxy
      apply (orderedFaceRealizationHomeomorph L s hs.1 hn).injective
      apply Subtype.ext
      have he (z : SSet.toTop.obj (Δ[n] : SSet.{u})) :=
        congrArg Subtype.val (ConcreteCategory.congr_hom
          (orderedFaceCellMap_geometricRealizationMap L s hs.1 hn) z)
      exact (he x).symm.trans ((congrArg Subtype.val hxy).trans (he y))
    · intro x y hxy
      apply hOld
      apply Subtype.ext
      have he (z : SSet.toTop.obj
          (orderedSimplicialSet (geometricFaceCostar L s).toPreAbstractSimplicialComplex)) :=
        congrArg Subtype.val (ConcreteCategory.congr_hom
          (geometricRealizationMap_inclusion (geometricFaceCostar_le L s)) z)
      exact (he x).symm.trans ((congrArg Subtype.val hxy).trans (he y))
    · intro x y hxy
      apply (orderedFaceCellMap_geometricRealizationMap_mem_costar_iff L s hs.1 hn x).mp
      have he := congrArg Subtype.val (ConcreteCategory.congr_hom
        (geometricRealizationMap_inclusion (geometricFaceCostar_le L s)) y)
      have hval := (congrArg Subtype.val hxy).trans he
      exact hval.symm ▸ (geometricRealizationMap (geometricFaceCostar L s) y).prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_injective ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_injective

def geometricRealizationHomeomorphism (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    SSet.toTop.obj (orderedSimplicialSet K.toPreAbstractSimplicialComplex) ≃ₜ K.space :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (geometricRealizationMap K)
      ⟨geometricRealizationMap_injective K, geometricRealizationMap_surjective K⟩)
    (geometricRealizationMap K).hom.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism


@[simp]
theorem geometricRealizationHomeomorphism_apply (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (x : SSet.toTop.obj (orderedSimplicialSet K.toPreAbstractSimplicialComplex)) :
    geometricRealizationHomeomorphism K x = geometricRealizationMap K x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_apply

@[reassoc]
theorem geometricRealizationHomeomorphism_inclusion
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] (h : K ≤ L) :
    SSet.toTop.map (orderedInclusion h) ≫
        (TopCat.isoOfHomeo (geometricRealizationHomeomorphism L)).hom =
      (TopCat.isoOfHomeo (geometricRealizationHomeomorphism K)).hom ≫ geometricInclusion h :=
  geometricRealizationMap_inclusion h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_inclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism_inclusion

end DifferentialGeometry.Topology.SimplicialComplex
