import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Data.Finset.Sort

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.Simplicial _root_.Opposite
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι] (K : PreAbstractSimplicialComplex ι)


def orderedNerveSubcomplex : (_root_.CategoryTheory.nerve ι).Subcomplex where
  obj n := {x | Finset.univ.image x.obj ∈ K}
  map {m n} f x hx := by
    apply (K.isRelLowerSet_faces hx).2
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨f.unop.toOrderHom i, Finset.mem_univ _, rfl⟩
    · exact Finset.image_nonempty.mpr Finset.univ_nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex

def orderedSimplicialSet : SSet.{u} := orderedNerveSubcomplex K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet


theorem mem_orderedNerveSubcomplex_iff {n : SimplexCategoryᵒᵖ} (x : (_root_.CategoryTheory.nerve ι).obj n) :
    x ∈ (orderedNerveSubcomplex K).obj n ↔ Finset.univ.image x.obj ∈ K := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_orderedNerveSubcomplex_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_orderedNerveSubcomplex_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_orderedNerveSubcomplex_iff ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_orderedNerveSubcomplex_iff


theorem orderedSimplicialSet_mem_nonDegenerate_iff {n : ℕ}
    (x : (orderedSimplicialSet K) _⦋n⦌) :
    x ∈ (orderedSimplicialSet K).nonDegenerate n ↔ StrictMono x.val.obj := by
  exact ((orderedNerveSubcomplex K).mem_nonDegenerate_iff x).trans
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono x.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_mem_nonDegenerate_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_mem_nonDegenerate_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_mem_nonDegenerate_iff ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_mem_nonDegenerate_iff


theorem card_vertices_nondegenerate {n : ℕ}
    (x : (orderedSimplicialSet K).nonDegenerate n) :
    (Finset.univ.image x.val.val.obj).card = n + 1 := by
  rw [Finset.card_image_of_injective _
    ((orderedSimplicialSet_mem_nonDegenerate_iff K x.val).mp x.prop).injective]
  exact Fintype.card_fin _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_vertices_nondegenerate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_vertices_nondegenerate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_vertices_nondegenerate ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_vertices_nondegenerate

def orderedSimplexOfFace {n : ℕ} (s : Finset ι) (hs : s ∈ K) (hn : s.card = n + 1) :
    (orderedSimplicialSet K).nonDegenerate n := by
  let x : _root_.CategoryTheory.ComposableArrows ι n := (s.orderEmbOfFin hn).monotone.functor
  have hx : Finset.univ.image x.obj ∈ K := by
    change Finset.univ.image (s.orderEmbOfFin hn) ∈ K
    rw [Finset.image_orderEmbOfFin_univ]
    exact hs
  refine ⟨⟨x, hx⟩, (orderedSimplicialSet_mem_nonDegenerate_iff K _).mpr ?_⟩
  exact (s.orderEmbOfFin hn).strictMono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplexOfFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedSimplexOfFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplexOfFace ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedSimplexOfFace


@[simp]
theorem vertices_orderedSimplexOfFace {n : ℕ} (s : Finset ι) (hs : s ∈ K)
    (hn : s.card = n + 1) :
    Finset.univ.image (orderedSimplexOfFace K s hs hn).val.val.obj = s :=
  Finset.image_orderEmbOfFin_univ s hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.vertices_orderedSimplexOfFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.vertices_orderedSimplexOfFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.vertices_orderedSimplexOfFace ``Submission.DifferentialGeometry.Topology.SimplicialComplex.vertices_orderedSimplexOfFace

def orderedNondegenerateFaceEquiv (n : ℕ) :
    (orderedSimplicialSet K).nonDegenerate n ≃ {s : Finset ι // s ∈ K ∧ s.card = n + 1} where
  toFun x := ⟨Finset.univ.image x.val.val.obj, x.val.prop, card_vertices_nondegenerate K x⟩
  invFun s := orderedSimplexOfFace K s.val s.prop.1 s.prop.2
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply nerve.ext_of_isThin
    exact (Finset.orderEmbOfFin_unique (card_vertices_nondegenerate K x)
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ((orderedSimplicialSet_mem_nonDegenerate_iff K x.val).mp x.prop)).symm
  right_inv s := Subtype.ext (vertices_orderedSimplexOfFace K s.val s.prop.1 s.prop.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedNondegenerateFaceEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedNondegenerateFaceEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedNondegenerateFaceEquiv ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedNondegenerateFaceEquiv


theorem orderedSimplicialSet_hasDimensionLT (d : ℕ) (hd : ∀ s ∈ K, s.card ≤ d) :
    (orderedSimplicialSet K).HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext x
    simp only [SSet.mem_degenerate_iff_notMem_nonDegenerate, Set.top_eq_univ,
      Set.mem_univ, iff_true]
    intro hx
    have hc := card_vertices_nondegenerate K ⟨x, hx⟩
    change (Finset.univ.image x.val.obj).card = n + 1 at hc
    have hbound := hd _ x.prop
    omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_hasDimensionLT then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_hasDimensionLT"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_hasDimensionLT ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_hasDimensionLT

instance finite_orderedSimplicialSet [Finite K.faces] : (orderedSimplicialSet K).Finite := by
  classical
  let S := (Set.toFinite K.faces).toFinset
  let d := S.sup Finset.card
  have hd : ∀ s ∈ K, s.card ≤ d := by
    intro s hs
    exact Finset.le_sup (f := Finset.card) ((Set.toFinite K.faces).mem_toFinset.mpr hs)
  have : (orderedSimplicialSet K).HasDimensionLT d := orderedSimplicialSet_hasDimensionLT K d hd
  apply SSet.finite_of_hasDimensionLT _ d
  intro n _
  have : Finite {s : Finset ι // s ∈ K ∧ s.card = n + 1} :=
    Finite.of_injective (fun s => (⟨s.val, s.prop.1⟩ : K.faces))
      (fun _ _ h => Subtype.ext (congrArg (fun t : K.faces => t.val) h))
  exact Finite.of_equiv _ (orderedNondegenerateFaceEquiv K n).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finite_orderedSimplicialSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finite_orderedSimplicialSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finite_orderedSimplicialSet ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finite_orderedSimplicialSet

end DifferentialGeometry.Topology.SimplicialComplex
