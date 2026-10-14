import Submission.DifferentialGeometry.Topology.SimplicialSet.CellAttachment
import Submission.DifferentialGeometry.Topology.SimplicialSet.RelativeRealization
import Submission.DifferentialGeometry.Topology.Homology.Algebra.QuasiIsoMiddle
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Simplicial

universe u

namespace DifferentialGeometry.SSet

theorem isIso_realizationChainMap_of_isEmpty {k : Type u} [Ring k]
    (R : ModuleCat.{u} k) (X : _root_.SSet.{u}) [IsEmpty (_root_.SSet.toTop.obj X)] :
    IsIso (realizationChainMap X R) := by
  have he (m : ℕ) (x : (TopCat.toSSet.obj (_root_.SSet.toTop.obj X)) _⦋m⦌) : False :=
    isEmptyElim ((show SimplexCategory.toTop.obj ⦋m⦌ ⟶ _root_.SSet.toTop.obj X from x.down)
      (Classical.ofNonempty : SimplexCategory.toTop.obj ⦋m⦌))
  have hs (m : ℕ) : _root_.CategoryTheory.Limits.IsZero ((X.chainComplex R).X m) := by
    rw [IsZero.iff_id_eq_zero]
    apply _root_.SSet.chainComplex_hom_ext
    intro x
    exact (he m ((sSetTopAdj.unit.app X).app _ x)).elim
  have ht (m : ℕ) :
      IsZero (((TopCat.toSSet.obj (_root_.SSet.toTop.obj X)).chainComplex R).X m) := by
    rw [IsZero.iff_id_eq_zero]
    apply _root_.SSet.chainComplex_hom_ext
    intro x
    exact (he m x).elim
  have (m : ℕ) : _root_.CategoryTheory.IsIso ((realizationChainMap X R).f m) := (hs m).isIso (ht m) _
  exact _root_.HomologicalComplex.Hom.isIso_of_components _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isIso_realizationChainMap_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isIso_realizationChainMap_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isIso_realizationChainMap_of_isEmpty ``Submission.DifferentialGeometry.SSet.isIso_realizationChainMap_of_isEmpty

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  {n : ℕ} {X Y : _root_.SSet.{u}}
  {g : (_root_.SSet.boundary n : _root_.SSet) ⟶ X}
  {r : (Δ[n] : _root_.SSet) ⟶ Y} {b : X ⟶ Y}
  (h : IsPushout (_root_.SSet.boundary n).ι g r b)

include h

theorem isIso_relativeSimplicialChainMap_of_isPushout :
    IsIso (relativeSimplicialChainMap R h.w) := by
  exact _root_.CategoryTheory.Limits.isIso_cokernel_map_of_isPushout
    (h.map ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isIso_relativeSimplicialChainMap_of_isPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isIso_relativeSimplicialChainMap_of_isPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isIso_relativeSimplicialChainMap_of_isPushout ``Submission.DifferentialGeometry.SSet.isIso_relativeSimplicialChainMap_of_isPushout

theorem relativeRealizationChainMap_cell :
    relativeSimplicialChainMap R h.w ≫ relativeRealizationChainMap R b =
      relativeRealizationChainMap R (_root_.SSet.boundary n).ι ≫
        realizedCellRelativeChainMap R h :=
  relativeRealizationChainMap_naturality R h.w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeRealizationChainMap_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeRealizationChainMap_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeRealizationChainMap_cell ``Submission.DifferentialGeometry.SSet.relativeRealizationChainMap_cell

theorem quasiIso_relativeRealizationChainMap_of_cell
    (hBoundary : QuasiIso (realizationChainMap (_root_.SSet.boundary n : _root_.SSet) R)) :
    QuasiIso (relativeRealizationChainMap R b) := by
  have : _root_.CategoryTheory.IsIso (relativeSimplicialChainMap R h.w) :=
    isIso_relativeSimplicialChainMap_of_isPushout R h
  have : QuasiIso (relativeRealizationChainMap R (_root_.SSet.boundary n).ι) :=
    quasiIso_relativeRealizationChainMap R _ (isClosedEmbedding_toTop_boundaryι n).isEmbedding
      hBoundary (quasiIso_realizationChainMap_stdSimplex n R)
  have : QuasiIso (realizedCellRelativeChainMap R h) :=
    quasiIso_realizedCellRelativeChainMap R h
  have : QuasiIso (relativeSimplicialChainMap R h.w ≫ relativeRealizationChainMap R b) := by
    rw [relativeRealizationChainMap_cell R h]
    exact quasiIso_comp _ _
  exact quasiIso_of_comp_left (relativeSimplicialChainMap R h.w) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap_of_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap_of_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap_of_cell ``Submission.DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap_of_cell

theorem quasiIso_realizationChainMap_of_cell
    (hBoundary : QuasiIso (realizationChainMap (_root_.SSet.boundary n : _root_.SSet) R))
    (hX : QuasiIso (realizationChainMap X R)) :
    QuasiIso (realizationChainMap Y R) := by
  have : _root_.CategoryTheory.Mono b := Adhesive.mono_of_isPushout_of_mono_left h
  have : _root_.CategoryTheory.Mono (_root_.SSet.chainComplexMap b R) := by
    unfold _root_.SSet.chainComplexMap
    infer_instance
  have : _root_.CategoryTheory.IsIso (realizationToRange b) :=
    isIso_realizationToRange b (isClosedEmbedding_toTop_attachment h).isEmbedding
  have : QuasiIso (realizationChainMap X R) := hX
  exact DifferentialGeometry.HomologicalComplex.quasiIso_middle (relativeRealizationShortComplexMap R b)
    (DifferentialGeometry.HomologicalComplex.cokernelSequence_shortExact _)
    (DifferentialGeometry.Homology.relativeShortExact _ _ R)
    (quasiIso_comp (realizationChainMap X R)
      (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange b)))
    (quasiIso_relativeRealizationChainMap_of_cell R h hBoundary)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.quasiIso_realizationChainMap_of_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.quasiIso_realizationChainMap_of_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.quasiIso_realizationChainMap_of_cell ``Submission.DifferentialGeometry.SSet.quasiIso_realizationChainMap_of_cell

end DifferentialGeometry.SSet
