import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreCutChainProducer
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreComponent
import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private def middleBandIntervalInclusion : _root_.Set.Ioo (-1 : ℝ) 1 → _root_.Set.Icc (-2 : ℝ) 2 :=
  fun t => ⟨t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandIntervalInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandIntervalInclusion target :: scope.openDecls } }

private theorem middleBandIntervalInclusion_isEmbedding :
    _root_.Topology.IsEmbedding middleBandIntervalInclusion := by
  apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact _root_.Topology.IsEmbedding.subtypeVal

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandIntervalInclusion_isEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandIntervalInclusion_isEmbedding target :: scope.openDecls } }

private def middleBandInclusion : Sphere 2 × _root_.Set.Ioo (-1 : ℝ) 1 → TubeDomain :=
  Prod.map id middleBandIntervalInclusion

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandInclusion target :: scope.openDecls } }

private theorem middleBandInclusion_isEmbedding :
    _root_.Topology.IsEmbedding middleBandInclusion :=
  _root_.Topology.IsEmbedding.id.prodMap middleBandIntervalInclusion_isEmbedding

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandInclusion_isEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.middleBandInclusion_isEmbedding target :: scope.openDecls } }

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

private theorem range_tube_middleBandInclusion (a : T.Index) :
    Set.range (T.tube a ∘ middleBandInclusion) = T.removedBand a := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨middleBandInclusion z, z.2.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z.1, ⟨z.2.1, hz⟩), ?_⟩
    congr 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_middleBandInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.range_tube_middleBandInclusion target :: scope.openDecls } }

private theorem tube_middleBandInclusion_isOpenEmbedding (a : T.Index)
    (hopen : IsOpen (T.removedBand a)) :
    _root_.Topology.IsOpenEmbedding (T.tube a ∘ middleBandInclusion) :=
  ⟨(T.embedding a).comp middleBandInclusion_isEmbedding,
    (T.range_tube_middleBandInclusion a).symm ▸ hopen⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.tube_middleBandInclusion_isOpenEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.tube_middleBandInclusion_isOpenEmbedding target :: scope.openDecls } }

def middleSphereCollar (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
      (fun y : Sphere 2 => T.tube a (y, (⟨0, by norm_num⟩ : _root_.Set.Icc (-2 : ℝ) 2))) :=
  DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.ofOpenInterval one_pos
    (T.tube a ∘ middleBandInclusion)
    (T.tube_middleBandInclusion_isOpenEmbedding a hopen)
    (by intro y; rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar

@[simp] theorem middleSphereCollar_zero (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2) :
    (T.middleSphereCollar a hopen).toFun (y, 0) = T.tube a (y, (⟨0, by norm_num⟩ : _root_.Set.Icc (-2 : ℝ) 2)) :=
  (T.middleSphereCollar a hopen).zero_eq y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero

theorem middleSphereCollar_range (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    (T.middleSphereCollar a hopen).range = T.removedBand a := by
  let h : Sphere 2 × ℝ ≃ₜ Sphere 2 × _root_.Set.Ioo (-1 : ℝ) 1 :=
    (Homeomorph.refl (Sphere 2)).prodCongr
      (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo 1 one_pos)
  change Set.range ((T.tube a ∘ middleBandInclusion) ∘ h) = _
  rw [h.surjective.range_comp]
  exact T.range_tube_middleBandInclusion a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_range

theorem middleSphereCollar_toFun (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2) (t : ℝ) :
    (T.middleSphereCollar a hopen).toFun (y, t) =
      T.tube a (y, ⟨
        (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
          1 one_pos t : Set.Ioo (-1 : ℝ) 1).1,
        by
          have ht := (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
            1 one_pos t : Set.Ioo (-1 : ℝ) 1).2
          constructor <;> linarith [ht.1, ht.2]⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_toFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_toFun

theorem middleSphereCollar_mem_positiveTube (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2)
    {t : ℝ} (ht : 0 < t) :
    (T.middleSphereCollar a hopen).toFun (y, t) ∈ T.positiveTube a := by
  let r := DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
    1 one_pos t
  refine ⟨(y, middleBandIntervalInclusion r), ?_, rfl⟩
  exact (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_pos_iff
    1 one_pos t).mpr ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_positiveTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_positiveTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_positiveTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_positiveTube

theorem middleSphereCollar_mem_negativeTube (a : T.Index) (hopen : IsOpen (T.removedBand a))
    (y : Sphere 2)
    {t : ℝ} (ht : t < 0) :
    (T.middleSphereCollar a hopen).toFun (y, t) ∈ T.negativeTube a := by
  let r := DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo
    1 one_pos t
  refine ⟨(y, middleBandIntervalInclusion r), ?_, rfl⟩
  exact (DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.realHomeomorphIoo_neg_iff
    1 one_pos t).mpr ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_negativeTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_negativeTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_negativeTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_mem_negativeTube

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)
    (hopen : ∀ a, IsOpen (T.removedBand a))

theorem pairwise_disjoint_middleSphereCollar_range :
    Pairwise fun a b => Disjoint (T.middleSphereCollar a (hopen a)).range
      (T.middleSphereCollar b (hopen b)).range := by
  intro a b hab
  rw [T.middleSphereCollar_range, T.middleSphereCollar_range]
  exact (T.disjoint hab).mono (T.removedBand_subset_range a) (T.removedBand_subset_range b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.pairwise_disjoint_middleSphereCollar_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.pairwise_disjoint_middleSphereCollar_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.pairwise_disjoint_middleSphereCollar_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.pairwise_disjoint_middleSphereCollar_range

theorem middleSphereCollar_zero_range (a : T.Index) :
    Set.range (fun y : Sphere 2 => (T.middleSphereCollar a (hopen a)).toFun (y, 0)) =
      T.middleSphere a := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    dsimp only
    rw [T.middleSphereCollar_zero]
    exact ⟨_, rfl, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    dsimp only
    rw [T.middleSphereCollar_zero]
    apply congrArg (T.tube a)
    exact Prod.ext rfl (Subtype.ext hz.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_zero_range

theorem puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range :
    T.puncturedCore =
      (⋃ a, Set.range (fun y : Sphere 2 => (T.middleSphereCollar a (hopen a)).toFun (y, 0)))ᶜ := by
  simp_rw [T.middleSphereCollar_zero_range]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end

noncomputable section

open _root_.Set _root_.Submission.Set
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace TubeSystem
variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem isConnected_positiveTube (a : T.Index) : IsConnected (T.positiveTube a) := by
  let f : Sphere 2 × _root_.Set.Ioc (0 : ℝ) 2 → M := fun z =>
    T.tube a (z.1, ⟨z.2.1, by
      exact ⟨by linarith [z.2.2.1], z.2.2.2⟩⟩)
  have hi : ConnectedSpace (_root_.Set.Ioc (0 : ℝ) 2) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioc (by norm_num))
  have hs : ConnectedSpace (Sphere 2) := inferInstanceAs
    (ConnectedSpace DifferentialGeometry.Topology.SphereTwo)
  have hf : Continuous f := by
    apply (T.tube a).continuous.comp
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hrange : Set.range f = T.positiveTube a := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, z.2.2.1, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z.1, ⟨z.2.1, hz, z.2.2.2⟩), rfl⟩
  rw [← hrange]
  exact isConnected_range hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_positiveTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_positiveTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_positiveTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_positiveTube

theorem isConnected_negativeTube (a : T.Index) : IsConnected (T.negativeTube a) := by
  let f : Sphere 2 × _root_.Set.Ico (-2 : ℝ) 0 → M := fun z =>
    T.tube a (z.1, ⟨z.2.1, by
      exact ⟨z.2.2.1, by linarith [z.2.2.2]⟩⟩)
  have hi : ConnectedSpace (_root_.Set.Ico (-2 : ℝ) 0) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ico (by norm_num))
  have hs : ConnectedSpace (Sphere 2) := inferInstanceAs
    (ConnectedSpace DifferentialGeometry.Topology.SphereTwo)
  have hf : Continuous f := by
    apply (T.tube a).continuous.comp
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hrange : Set.range f = T.negativeTube a := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, z.2.2.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z.1, ⟨z.2.1, z.2.2.1, hz⟩), rfl⟩
  rw [← hrange]
  exact isConnected_range hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_negativeTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_negativeTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_negativeTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.isConnected_negativeTube
end TubeSystem
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

private theorem middleSphereCollar_complement (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    (T.middleSphereCollar a hopen).complement = (T.middleSphere a)ᶜ := by
  change (Set.range (fun y : Sphere 2 => T.tube a (y, middleLevel)))ᶜ = _
  rw [show (fun y : Sphere 2 => T.tube a (y, middleLevel)) =
    (fun y : Sphere 2 => T.tube a (middleSphereSlice y)) from rfl,
    T.range_tube_middleSphereSlice]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_complement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereCollar_complement target :: scope.openDecls } }

def middleSphereSides [T2Space M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]
    (a : T.Index) (hopen : IsOpen (T.removedBand a)) :
    T.MiddleSphereSides a := by
  let h := T.middleSphereCollar a hopen
  let : ConnectedSpace (Sphere 2) :=
    inferInstanceAs (ConnectedSpace DifferentialGeometry.Topology.SphereTwo)
  let y : Sphere 2 := DifferentialGeometry.Topology.sphereTwoNorth
  refine
    { A := h.positiveSide
      B := h.negativeSide
      isOpen_A := h.isOpen_positiveSide
      isOpen_B := h.isOpen_negativeSide
      disjoint := h.disjoint_negativeSide_positiveSide.symm
      union_eq := ?_
      positiveTube_subset := ?_
      negativeTube_subset := ?_ }
  · rw [Set.union_comm, ← h.complement_eq_negativeSide_union_positiveSide]
    exact T.middleSphereCollar_complement a hopen
  · have hsub : T.positiveTube a ⊆ h.positiveSide ∪ h.negativeSide := by
      rw [Set.union_comm, ← h.complement_eq_negativeSide_union_positiveSide,
        T.middleSphereCollar_complement]
      intro x hx hm
      exact (T.mem_puncturedCore_iff x).mp
        (T.positiveTube_subset_puncturedCore a hx) a hm
    exact (T.isConnected_positiveTube a).isPreconnected.subset_left_of_subset_union
      h.isOpen_positiveSide h.isOpen_negativeSide h.disjoint_negativeSide_positiveSide.symm
      hsub ⟨h.toFun (y, 1), T.middleSphereCollar_mem_positiveTube a hopen y (by norm_num),
        h.toFun_mem_positiveSide_of_pos y (by norm_num)⟩
  · have hsub : T.negativeTube a ⊆ h.positiveSide ∪ h.negativeSide := by
      rw [Set.union_comm, ← h.complement_eq_negativeSide_union_positiveSide,
        T.middleSphereCollar_complement]
      intro x hx hm
      exact (T.mem_puncturedCore_iff x).mp
        (T.negativeTube_subset_puncturedCore a hx) a hm
    exact (T.isConnected_negativeTube a).isPreconnected.subset_right_of_subset_union
      h.isOpen_positiveSide h.isOpen_negativeSide h.disjoint_negativeSide_positiveSide.symm
      hsub ⟨h.toFun (y, -1), T.middleSphereCollar_mem_negativeTube a hopen y (by norm_num),
        h.toFun_mem_negativeSide_of_neg y (by norm_num)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSides ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSides

theorem middleSphereSeparation_of_isOpen_removedBand
    [T2Space M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]
    (hopen : ∀ a, IsOpen (T.removedBand a)) : T.middleSphereSeparation :=
  fun a => ⟨T.middleSphereSides a (hopen a)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSeparation_of_isOpen_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSeparation_of_isOpen_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSeparation_of_isOpen_removedBand ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.middleSphereSeparation_of_isOpen_removedBand

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [T2Space M]
    [LocallyPathConnectedSpace M] [SimplyConnectedSpace M] (T : TubeSystem M)

theorem simplyConnectedSpace_connectedComponentIn_puncturedCore
    (hopen : ∀ a, IsOpen (T.removedBand a))
    {x : M} (hx : x ∈ T.puncturedCore) :
    SimplyConnectedSpace ↥(connectedComponentIn T.puncturedCore x) := by
  let _ : SimplyConnectedSpace (Sphere 2) :=
    DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace
  have heq := T.puncturedCore_eq_compl_iUnion_middleSphereCollar_zero_range hopen
  simp only [T.middleSphereCollar_zero] at heq
  rw [heq] at hx ⊢
  exact DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.simplyConnectedSpace_connectedComponentIn_compl_iUnion
    (fun a => T.middleSphereCollar a (hopen a))
    (T.pairwise_disjoint_middleSphereCollar_range hopen) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_connectedComponentIn_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_connectedComponentIn_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_connectedComponentIn_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.simplyConnectedSpace_connectedComponentIn_puncturedCore

theorem componentwiseSimplyConnected_of_isOpen_removedBand
    (hopen : ∀ a, IsOpen (T.removedBand a)) :
    T.componentwiseSimplyConnected := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : {y : ↥T.puncturedCore | ConnectedComponents.mk y = ConnectedComponents.mk x} =
      connectedComponent x := connectedComponents_preimage_singleton
  change SimplyConnectedSpace {y : ↥T.puncturedCore |
    ConnectedComponents.mk y = ConnectedComponents.mk x}
  rw [hset]
  exact (DifferentialGeometry.Topology.simplyConnectedSpace_connectedComponentIn_iff x.2).mp
    (T.simplyConnectedSpace_connectedComponentIn_puncturedCore hopen x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isOpen_removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isOpen_removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isOpen_removedBand ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isOpen_removedBand

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end
