import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Metric _root_.Submission.Metric _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

structure CutCapTransitionData (P Q D N : OrientedThreeStage.{u}) where
  trace : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier
  source_nonempty : Nonempty P.Carrier
  tube_smooth :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ∀ a : trace.tubes.Index,
      _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (trace.tubes.tube a)
  [coreCharts : ChartedSpace (EuclideanHalfSpace 3) trace.tubes.core]
  [coreSmooth : IsManifold (𝓡∂ 3) ∞ trace.tubes.core]
  core_induced : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
    (Subtype.val : trace.tubes.core → P.Carrier)
  core_boundary : (𝓡∂ 3).boundary trace.tubes.core =
    ⋃ b : trace.tubes.Boundary, Set.range (trace.tubes.coreBoundarySphere b)
  core_inclusion_smooth : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ trace.capping.coreInclusion
  cap_smooth : ∀ b, _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (trace.capping.cap b)
  attaching : ∀ _b : trace.tubes.Boundary, Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2
  attaching_eq : ∀ b, (attaching b : Sphere 2 → Sphere 2) = trace.capping.attaching b
  core_positive : ∀ x : trace.tubes.core, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : trace.tubes.core → P.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : trace.tubes.core → P.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x).toLinearMap hj))
        (P.orientation.orientation x.1) =
          N.orientation.orientation (trace.capping.coreInclusion x)
  cap_positive : ∀ b, ∀ x : ThreeBall, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (trace.capping.cap b x)
  presentation : N.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ (Q.Carrier ⊕ D.Carrier)
  presentation_eq : (presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = trace.presentation
  presentation_positive : ∀ x : N.Carrier,
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel presentation x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel presentation x).toLinearMap hf)
        (N.orientation.orientation x) =
          match presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData

def CutCapTransitionData.toSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (S : CutCapTransitionData P Q D N) : SmoothCutCapTransition P Q D N where
  trace := S.trace
  source_nonempty := S.source_nonempty
  tube_smooth := S.tube_smooth
  coreCharts := S.coreCharts
  coreSmooth := S.coreSmooth
  core_induced := S.core_induced
  core_boundary := S.core_boundary
  core_inclusion_smooth := S.core_inclusion_smooth
  ballCharts := threeBallChartedSpace
  ballSmooth := threeBall_isManifold
  ball_induced := isSmoothEmbedding_threeBall_inclusion
  ball_boundary := threeBall_boundary_eq_sphere
  cap_smooth := S.cap_smooth
  attaching := S.attaching
  attaching_eq := S.attaching_eq
  core_positive := S.core_positive
  cap_positive := S.cap_positive
  presentation := S.presentation
  presentation_eq := S.presentation_eq
  presentation_positive := S.presentation_positive

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.toSmoothCutCapTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.toSmoothCutCapTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.toSmoothCutCapTransition ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.toSmoothCutCapTransition

theorem nonempty_smoothCutCapTransition_of_data {P Q D N : OrientedThreeStage.{u}}
    (S : CutCapTransitionData P Q D N) : Nonempty (SmoothCutCapTransition P Q D N) :=
  ⟨S.toSmoothCutCapTransition⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_data then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_data"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_data ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition_of_data

def emptyTubeSystem (M : Type*) [TopologicalSpace M] : TubeSystem M where
  Index := PEmpty
  finiteIndex := ⟨∅, fun x => PEmpty.elim x⟩
  tube := fun a => PEmpty.elim a
  embedding := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem

theorem emptyTubeSystem_core (M : Type*) [TopologicalSpace M] :
    (emptyTubeSystem M).core = univ := by
  apply Set.eq_univ_of_forall
  intro x
  simp only [TubeSystem.core, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  intro a
  exact PEmpty.elim a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeSystem_core

def emptyTubeCapping (N : Type*) [TopologicalSpace N] :
    Capping (emptyTubeSystem N) N where
  coreInclusion := ⟨Subtype.val, continuous_subtype_val⟩
  coreEmbedding := Topology.IsEmbedding.subtypeVal
  cap := fun b => PEmpty.elim b.1
  capEmbedding := fun b => PEmpty.elim b.1
  attaching := fun b => PEmpty.elim b.1
  boundary_eq := fun b => PEmpty.elim b.1
  exhaustive := by
    have hcap : (⋃ b : (emptyTubeSystem N).Boundary,
        Set.range (PEmpty.elim b.1 : C(ThreeBall, N))) = ∅ := by
      apply Set.iUnion_eq_empty.mpr
      intro b
      exact PEmpty.elim b.1
    rw [hcap, Set.union_empty]
    apply Set.range_eq_univ.mpr
    intro x
    exact ⟨⟨x, by rw [emptyTubeSystem_core]; exact Set.mem_univ x⟩, rfl⟩
  core_cap_intersection := fun b => PEmpty.elim b.1
  cap_disjoint := fun b => PEmpty.elim b.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeCapping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeCapping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeCapping ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTubeCapping

def discardedComponentCutCap (Q D : Type*) [TopologicalSpace Q] [TopologicalSpace D]
    (d : D) : CutCapTopology (Q ⊕ D) Q D (Q ⊕ D) where
  tubes := emptyTubeSystem (Q ⊕ D)
  capping := emptyTubeCapping (Q ⊕ D)
  presentation := Homeomorph.refl _
  nontrivial := Or.inr ⟨d⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap

theorem discardedComponentCutCap_retained (Q D : Type*) [TopologicalSpace Q]
    [TopologicalSpace D] (d : D) (q : Q) :
    (discardedComponentCutCap Q D d).presentation (Sum.inl q) = Sum.inl q ∧
      (discardedComponentCutCap Q D d).presentation (Sum.inr d) = Sum.inr d :=
  ⟨rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.discardedComponentCutCap_retained

theorem nonempty_retainedCore_of_discardedComponentCutCap (Q D : Type*)
    [TopologicalSpace Q] [TopologicalSpace D] (d : D) (q : Q) :
    Nonempty ((discardedComponentCutCap Q D d).retainedCore) := by
  refine ⟨⟨⟨Sum.inl q, ?_⟩, q, ?_⟩⟩
  · change Sum.inl q ∈ (emptyTubeSystem (Q ⊕ D)).core
    rw [emptyTubeSystem_core]
    exact Set.mem_univ _
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_retainedCore_of_discardedComponentCutCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_retainedCore_of_discardedComponentCutCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_retainedCore_of_discardedComponentCutCap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_retainedCore_of_discardedComponentCutCap

structure CutCapTopologyIgnoringNontrivial (M Q D N : Type*) [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace D] [TopologicalSpace N] where
  tubes : TubeSystem M
  capping : Capping tubes N
  presentation : N ≃ₜ Q ⊕ D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopologyIgnoringNontrivial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopologyIgnoringNontrivial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopologyIgnoringNontrivial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopologyIgnoringNontrivial

def vacuousCutCapTopology (M : Type*) [TopologicalSpace M] :
    CutCapTopologyIgnoringNontrivial (M ⊕ PEmpty) M PEmpty (M ⊕ PEmpty) where
  tubes := emptyTubeSystem (M ⊕ PEmpty)
  capping := emptyTubeCapping (M ⊕ PEmpty)
  presentation := Homeomorph.refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.vacuousCutCapTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.vacuousCutCapTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.vacuousCutCapTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.vacuousCutCapTopology

theorem not_isEmpty_index_and_isEmpty_discarded {M Q D N : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace D] [TopologicalSpace N]
    (E : CutCapTopology M Q D N) (h₁ : IsEmpty E.tubes.Index) (h₂ : IsEmpty D) : False := by
  rcases E.nontrivial with h | h
  · exact h₁.false h.some
  · exact h₂.false h.some

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_index_and_isEmpty_discarded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_index_and_isEmpty_discarded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_index_and_isEmpty_discarded ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_index_and_isEmpty_discarded

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FourSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FourSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FourSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FourSpace

def snocR {n : ℕ} (f : Fin n → ℝ) (a : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) f a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR

@[simp] theorem snocR_castSucc {n : ℕ} (f : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    snocR f a i.castSucc = f i := Fin.snoc_castSucc (α := fun _ => ℝ) a f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_castSucc ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_castSucc

@[simp] theorem snocR_last {n : ℕ} (f : Fin n → ℝ) (a : ℝ) :
    snocR f a (Fin.last n) = a := Fin.snoc_last (α := fun _ => ℝ) a f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_last ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.snocR_last

def neckPoint (x : Sphere 2) (t : ℝ) : FourSpace :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => Real.sqrt (1 - (t / 4) ^ 2) * x.1 i) (t / 4))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint

theorem neckPoint_mem_sphere (x : Sphere 2) (t : _root_.Set.Icc (-2 : ℝ) 2) :
    neckPoint x t.1 ∈ Sphere 3 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have habs : |t.1| ≤ 2 := abs_le.mpr ⟨t.2.1, t.2.2⟩
  have h4 : t.1 ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [habs, abs_nonneg t.1]
  have ht : (t.1 / 4) ^ 2 ≤ 1 := by nlinarith [h4]
  have hsqrt : Real.sqrt (1 - (t.1 / 4) ^ 2) ^ 2 = 1 - (t.1 / 4) ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    have h := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have h2 : ‖neckPoint x t.1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [neckPoint, WithLp.ofLp_toLp]
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin 3, ‖snocR (fun i : Fin 3 => Real.sqrt (1 - (t.1 / 4) ^ 2) * x.1 i)
        (t.1 / 4) i.castSucc‖ ^ 2)
        = (Real.sqrt (1 - (t.1 / 4) ^ 2)) ^ 2 * ∑ i : Fin 3, ‖x.1 i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [snocR_castSucc, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1, snocR_last, Real.norm_eq_abs, sq_abs,
      ← EuclideanSpace.norm_sq_eq (x : EuclideanSpace ℝ (Fin 3)), hx, hsqrt]
    ring
  nlinarith [norm_nonneg (neckPoint x t.1), h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint_mem_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint_mem_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint_mem_sphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckPoint_mem_sphere

def standardNeckTubeFun (z : TubeDomain) : Sphere 3 :=
  ⟨neckPoint z.1 z.2.1, neckPoint_mem_sphere z.1 z.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun

theorem continuous_snocR_family :
    Continuous fun z : TubeDomain =>
      (fun i : Fin 3 => Real.sqrt (1 - (z.2.1 / 4) ^ 2) * z.1.1 i) := by
  apply continuous_pi
  intro i
  have hc : Continuous fun z : TubeDomain => Real.sqrt (1 - (z.2.1 / 4) ^ 2) := by fun_prop
  have hx : Continuous fun z : TubeDomain => ((z.1 : Sphere 2) : EuclideanSpace ℝ (Fin 3)) i := by
    fun_prop
  exact hc.mul hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_snocR_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_snocR_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_snocR_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_snocR_family

theorem continuous_standardNeckTubeFun : Continuous standardNeckTubeFun := by
  apply Continuous.subtype_mk
  have hg : Continuous fun z : TubeDomain => z.2.1 / 4 :=
    (continuous_subtype_val.comp continuous_snd).div_const 4
  have hbase : Continuous fun z : TubeDomain =>
      snocR (fun i : Fin 3 => Real.sqrt (1 - (z.2.1 / 4) ^ 2) * z.1.1 i) (z.2.1 / 4) :=
    Continuous.finSnoc continuous_snocR_family hg
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_standardNeckTubeFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_standardNeckTubeFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_standardNeckTubeFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.continuous_standardNeckTubeFun

theorem standardNeckTubeFun_injective : Function.Injective standardNeckTubeFun := by
  intro z w hzw
  have hlast : z.2.1 / 4 = w.2.1 / 4 := by
    have h := congrArg (fun p : Sphere 3 => (p.1 : FourSpace).ofLp (Fin.last 3)) hzw
    simpa only [standardNeckTubeFun, neckPoint, WithLp.ofLp_toLp, snocR_last] using h
  have ht : z.2.1 = w.2.1 := by linarith
  have hpos : 0 < Real.sqrt (1 - (z.2.1 / 4) ^ 2) := by
    have habs : |z.2.1| ≤ 2 := abs_le.mpr ⟨z.2.2.1, z.2.2.2⟩
    have h4 : z.2.1 ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [habs, abs_nonneg z.2.1]
    apply Real.sqrt_pos.mpr
    nlinarith [h4]
  have hx : z.1 = w.1 := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    have h := congrArg (fun p : Sphere 3 => (p.1 : FourSpace).ofLp i.castSucc) hzw
    simp only [standardNeckTubeFun, neckPoint, WithLp.ofLp_toLp, snocR_castSucc] at h
    rw [← ht] at h
    exact mul_left_cancel₀ (ne_of_gt hpos) h
  exact Prod.ext hx (Subtype.ext ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeFun_injective

theorem isEmbedding_standardNeckTubeFun : Topology.IsEmbedding standardNeckTubeFun :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_standardNeckTubeFun
    standardNeckTubeFun_injective
    fun _s hs => (hs.isCompact.image continuous_standardNeckTubeFun).isClosed).toIsEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_standardNeckTubeFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_standardNeckTubeFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_standardNeckTubeFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isEmbedding_standardNeckTubeFun

def standardNeckTube : C(TubeDomain, Sphere 3) :=
  ⟨standardNeckTubeFun, continuous_standardNeckTubeFun⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTube

def standardNeckTubeSystem : TubeSystem (Sphere 3) where
  Index := PUnit
  finiteIndex := inferInstance
  tube := fun _ => standardNeckTube
  embedding := fun _ => isEmbedding_standardNeckTubeFun
  disjoint := fun a b hab => (hab (Subsingleton.elim a b)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem

theorem standardNeckTubeSystem_index_nonempty :
    Nonempty standardNeckTubeSystem.Index := ⟨PUnit.unit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_index_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_index_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_index_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_index_nonempty

theorem standardNeckTubeSystem_boundary_nonempty :
    Nonempty standardNeckTubeSystem.Boundary := ⟨(PUnit.unit, _root_.Bool.false)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundary_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundary_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundary_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundary_nonempty


theorem standardNeckTubeSystem_removedBand_nonempty :
    (standardNeckTubeSystem.removedBand PUnit.unit).Nonempty := by
  let x₀ : Sphere 2 := ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩
  let z₀ : TubeDomain := (x₀, ⟨0, by norm_num, by norm_num⟩)
  exact ⟨standardNeckTube z₀, z₀, ⟨by norm_num, by norm_num⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_nonempty

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
