import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Submission.DifferentialGeometry.Topology.SphereSeparation.StandardSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

variable {N : Type*} [TopologicalSpace N]


theorem isCompact_range_sphereTwo_of_continuous
    {e : SphereTwo → N} (he : Continuous e) :
    IsCompact (Set.range e) :=
  isCompact_range he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_continuous ``Submission.DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_continuous


theorem isCompact_range_sphereTwo_of_isSmoothEmbedding
    [ChartedSpace EuclideanThree N] {e : SphereTwo → N}
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    IsCompact (Set.range e) :=
  isCompact_range_sphereTwo_of_continuous he.contMDiff.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.isCompact_range_sphereTwo_of_isSmoothEmbedding

theorem isClosed_range_sphereTwo_of_isSmoothEmbedding
    [ChartedSpace EuclideanThree N] [T2Space N] {e : SphereTwo → N}
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    IsClosed (Set.range e) :=
  (isCompact_range_sphereTwo_of_isSmoothEmbedding he).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isClosed_range_sphereTwo_of_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isClosed_range_sphereTwo_of_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isClosed_range_sphereTwo_of_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.isClosed_range_sphereTwo_of_isSmoothEmbedding

theorem isImmersionAtOfComplement_real_of_isSmoothEmbedding
    [ChartedSpace EuclideanThree N] {e : SphereTwo → N}
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    Manifold.IsImmersionAtOfComplement ℝ (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x := by
  let h := he.isImmersion.isImmersionAt x
  let hc := h.isImmersionAtOfComplement_complement
  let inclusion : h.complement →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) × h.complement :=
    LinearMap.inr ℝ _ _
  let linearInclusion : h.complement →ₗ[ℝ] EuclideanThree :=
    hc.equiv.toLinearEquiv.toLinearMap.comp inclusion
  let _ : FiniteDimensional ℝ h.complement :=
    FiniteDimensional.of_injective linearInclusion
      (hc.equiv.injective.comp LinearMap.inr_injective)
  have heq := hc.equiv.toLinearEquiv.finrank_eq
  simp only [Module.finrank_prod, finrank_euclideanSpace_fin] at heq
  have hdim : Module.finrank ℝ h.complement = 1 := by omega
  exact hc.trans_F
    (ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isImmersionAtOfComplement_real_of_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isImmersionAtOfComplement_real_of_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isImmersionAtOfComplement_real_of_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.isImmersionAtOfComplement_real_of_isSmoothEmbedding

theorem writtenInCharts_sphereTwo
    {e : SphereTwo → N} {x : SphereTwo}
    [ChartedSpace EuclideanThree N]
    (h : Manifold.IsImmersionAtOfComplement ℝ (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e x) :
    Set.EqOn
      ((h.codChart : N → EuclideanThree) ∘ e ∘
        (h.domChart.symm : EuclideanSpace ℝ (Fin 2) → SphereTwo))
      (h.equiv ∘ fun z ↦ (z, 0)) h.domChart.target := by
  simpa [OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm] using h.writtenInCharts

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.writtenInCharts_sphereTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.writtenInCharts_sphereTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.writtenInCharts_sphereTwo ``Submission.DifferentialGeometry.Topology.SphereSeparation.writtenInCharts_sphereTwo

structure EmbeddedSphereNormalChart
    [ChartedSpace EuclideanThree N] (e : SphereTwo → N) (x : SphereTwo) where
  normalForm : Manifold.IsImmersionAtOfComplement ℝ (𝓡 2)
    (modelWithCornersSelf ℝ EuclideanThree) ∞ e x
  neighborhood : Set N
  isOpen_neighborhood : IsOpen neighborhood
  image_mem_neighborhood : e x ∈ neighborhood
  neighborhood_subset_codChart_source :
    neighborhood ⊆ normalForm.codChart.source
  tangent_mem_domChart_target : ∀ y ∈ neighborhood,
    (normalForm.equiv.symm (normalForm.codChart y)).1 ∈
      normalForm.domChart.target
  neighborhood_inter_range_subset_image :
    neighborhood ∩ Set.range e ⊆ e '' normalForm.domChart.source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart

theorem embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement
    [ChartedSpace EuclideanThree N] {e : SphereTwo → N} {x : SphereTwo}
    (he : _root_.Topology.IsEmbedding e)
    (h : Manifold.IsImmersionAtOfComplement ℝ (𝓡 2) (𝓡 3) ∞ e x) :
    Nonempty (EmbeddedSphereNormalChart e x) := by
  classical
  obtain ⟨W, hWopen, himage⟩ :=
    he.isInducing.image_eq_isOpen_inter_range
      h.domChart.open_source
  let strip : Set EuclideanThree :=
    h.equiv '' (h.domChart.target ×ˢ (Set.univ : Set ℝ))
  have hstripOpen : IsOpen strip := by
    exact h.equiv.toHomeomorph.isOpen_image.2
      (h.domChart.open_target.prod isOpen_univ)
  let O : Set N := W ∩
    (h.codChart.source ∩ h.codChart ⁻¹' strip)
  have hOopen : IsOpen O := by
    exact hWopen.inter (h.codChart.isOpen_inter_preimage hstripOpen)
  have hxImage : e x ∈ W ∩ Set.range e := by
    rw [← himage]
    exact ⟨x, h.mem_domChart_source, rfl⟩
  have hxTarget := h.domChart.map_source h.mem_domChart_source
  have hxNormal := writtenInCharts_sphereTwo h hxTarget
  have hxNormal' : h.codChart (e x) =
      h.equiv (h.domChart x, 0) := by
    simpa [Function.comp_apply,
      h.domChart.left_inv h.mem_domChart_source] using hxNormal
  have hxStrip : h.codChart (e x) ∈ strip := by
    refine ⟨(h.domChart x, 0), ⟨hxTarget, Set.mem_univ 0⟩, ?_⟩
    exact hxNormal'.symm
  have hxO : e x ∈ O :=
    ⟨hxImage.1, h.mem_codChart_source, hxStrip⟩
  have hOsource : O ⊆ h.codChart.source := by
    intro y hy
    exact hy.2.1
  have hOtangent : ∀ y ∈ O,
      (h.equiv.symm (h.codChart y)).1 ∈ h.domChart.target := by
    intro y hy
    rcases hy.2.2 with ⟨zr, hzr, hzrEq⟩
    rcases zr with ⟨z, r⟩
    have hz : z ∈ h.domChart.target := hzr.1
    rw [← hzrEq, h.equiv.symm_apply_apply]
    exact hz
  have hOrange : O ∩ Set.range e = e '' h.domChart.source := by
    apply Set.Subset.antisymm
    · intro y hy
      rw [himage]
      exact ⟨hy.1.1, hy.2⟩
    · rintro y ⟨m, hm, rfl⟩
      have hem : e m ∈ W ∩ Set.range e := by
        rw [← himage]
        exact ⟨m, hm, rfl⟩
      have hmTarget := h.domChart.map_source hm
      have hmNormal := writtenInCharts_sphereTwo h hmTarget
      have hmNormal' : h.codChart (e m) =
          h.equiv (h.domChart m, 0) := by
        simpa [Function.comp_apply,
          h.domChart.left_inv hm] using hmNormal
      have hmStrip : h.codChart (e m) ∈ strip := by
        refine ⟨(h.domChart m, 0), ⟨hmTarget, Set.mem_univ 0⟩, ?_⟩
        exact hmNormal'.symm
      exact ⟨⟨hem.1, h.source_subset_preimage_source hm, hmStrip⟩, hem.2⟩
  exact ⟨{
    normalForm := h
    neighborhood := O
    isOpen_neighborhood := hOopen
    image_mem_neighborhood := hxO
    neighborhood_subset_codChart_source := hOsource
    tangent_mem_domChart_target := hOtangent
    neighborhood_inter_range_subset_image := hOrange.subset
  }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement

theorem embeddedSphereNormalChart_nonempty
    [ChartedSpace EuclideanThree N] {e : SphereTwo → N}
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) : Nonempty (EmbeddedSphereNormalChart e x) :=
  embeddedSphereNormalChart_nonempty_of_isImmersionAtOfComplement he.isEmbedding
    (isImmersionAtOfComplement_real_of_isSmoothEmbedding he x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphereNormalChart_nonempty

namespace EmbeddedSphereNormalChart

variable [ChartedSpace EuclideanThree N] {e : SphereTwo → N}
  {x : SphereTwo}


noncomputable def normalCoordinate
    (c : EmbeddedSphereNormalChart e x) (y : N) : ℝ :=
  (c.normalForm.equiv.symm (c.normalForm.codChart y)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate


noncomputable def positiveHalf (c : EmbeddedSphereNormalChart e x) : Set N :=
  c.neighborhood ∩ {y | 0 < c.normalCoordinate y}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf


noncomputable def negativeHalf (c : EmbeddedSphereNormalChart e x) : Set N :=
  c.neighborhood ∩ {y | c.normalCoordinate y < 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf

theorem normalCoordinate_eq_zero_iff
    (c : EmbeddedSphereNormalChart e x) {y : N}
    (hy : y ∈ c.neighborhood) :
    c.normalCoordinate y = 0 ↔ y ∈ Set.range e := by
  constructor
  · intro hyZero
    let z : EuclideanSpace ℝ (Fin 2) :=
      (c.normalForm.equiv.symm (c.normalForm.codChart y)).1
    let m : SphereTwo := c.normalForm.domChart.symm z
    have hzTarget : z ∈ c.normalForm.domChart.target :=
      c.tangent_mem_domChart_target y hy
    have hmSource : m ∈ c.normalForm.domChart.source :=
      c.normalForm.domChart.map_target hzTarget
    have hnormal := writtenInCharts_sphereTwo c.normalForm hzTarget
    have hnormal' : c.normalForm.codChart (e m) =
        c.normalForm.equiv (z, 0) := by
      simpa [m, Function.comp_apply] using hnormal
    have hcoord : c.normalForm.codChart (e m) = c.normalForm.codChart y := by
      rw [hnormal']
      rw [← hyZero]
      exact c.normalForm.equiv.apply_symm_apply _
    have hemSource : e m ∈ c.normalForm.codChart.source :=
      c.normalForm.source_subset_preimage_source hmSource
    have hySource : y ∈ c.normalForm.codChart.source :=
      c.neighborhood_subset_codChart_source hy
    exact ⟨m, c.normalForm.codChart.injOn hemSource hySource hcoord⟩
  · intro hyRange
    have hyLocal : y ∈ e '' c.normalForm.domChart.source := by
      exact c.neighborhood_inter_range_subset_image ⟨hy, hyRange⟩
    rcases hyLocal with ⟨m, hmSource, rfl⟩
    have hzTarget := c.normalForm.domChart.map_source hmSource
    have hnormal := writtenInCharts_sphereTwo c.normalForm hzTarget
    have hnormal' : c.normalForm.codChart (e m) =
        c.normalForm.equiv (c.normalForm.domChart m, 0) := by
      simpa [Function.comp_apply,
        c.normalForm.domChart.left_inv hmSource] using hnormal
    change (c.normalForm.equiv.symm
      (c.normalForm.codChart (e m))).2 = 0
    rw [hnormal', c.normalForm.equiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate_eq_zero_iff ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.normalCoordinate_eq_zero_iff


theorem isOpen_positiveHalf (c : EmbeddedSphereNormalChart e x) :
    IsOpen c.positiveHalf := by
  let P : Set EuclideanThree :=
    {z | 0 < (c.normalForm.equiv.symm z).2}
  have hP : IsOpen P :=
    isOpen_lt continuous_const c.normalForm.equiv.symm.continuous.snd
  have hopen : IsOpen
      (c.normalForm.codChart.source ∩
        c.normalForm.codChart ⁻¹' P) :=
    c.normalForm.codChart.isOpen_inter_preimage hP
  have heq : c.positiveHalf = c.neighborhood ∩
      (c.normalForm.codChart.source ∩
        c.normalForm.codChart ⁻¹' P) := by
    ext y
    simp only [positiveHalf, normalCoordinate, _root_.Set.mem_inter_iff,
      _root_.Set.mem_ofPred_eq, _root_.Set.mem_preimage, P]
    constructor
    · rintro ⟨hy, hpos⟩
      exact ⟨hy, c.neighborhood_subset_codChart_source hy, hpos⟩
    · rintro ⟨hy, _, hpos⟩
      exact ⟨hy, hpos⟩
  rw [heq]
  exact c.isOpen_neighborhood.inter hopen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_positiveHalf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_positiveHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_positiveHalf ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_positiveHalf


theorem isOpen_negativeHalf (c : EmbeddedSphereNormalChart e x) :
    IsOpen c.negativeHalf := by
  let P : Set EuclideanThree :=
    {z | (c.normalForm.equiv.symm z).2 < 0}
  have hP : IsOpen P :=
    isOpen_lt c.normalForm.equiv.symm.continuous.snd continuous_const
  have hopen : IsOpen
      (c.normalForm.codChart.source ∩
        c.normalForm.codChart ⁻¹' P) :=
    c.normalForm.codChart.isOpen_inter_preimage hP
  have heq : c.negativeHalf = c.neighborhood ∩
      (c.normalForm.codChart.source ∩
        c.normalForm.codChart ⁻¹' P) := by
    ext y
    simp only [negativeHalf, normalCoordinate, _root_.Set.mem_inter_iff,
      _root_.Set.mem_ofPred_eq, _root_.Set.mem_preimage, P]
    constructor
    · rintro ⟨hy, hneg⟩
      exact ⟨hy, c.neighborhood_subset_codChart_source hy, hneg⟩
    · rintro ⟨hy, _, hneg⟩
      exact ⟨hy, hneg⟩
  rw [heq]
  exact c.isOpen_neighborhood.inter hopen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_negativeHalf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_negativeHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_negativeHalf ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isOpen_negativeHalf


theorem disjoint_positiveHalf_negativeHalf
    (c : EmbeddedSphereNormalChart e x) :
    Disjoint c.positiveHalf c.negativeHalf := by
  rw [Set.disjoint_left]
  rintro y ⟨_, hyPos⟩ ⟨_, hyNeg⟩
  change 0 < c.normalCoordinate y at hyPos
  change c.normalCoordinate y < 0 at hyNeg
  exact (not_lt_of_ge hyPos.le) hyNeg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.disjoint_positiveHalf_negativeHalf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.disjoint_positiveHalf_negativeHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.disjoint_positiveHalf_negativeHalf ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.disjoint_positiveHalf_negativeHalf


theorem positiveHalf_subset_compl_range
    (c : EmbeddedSphereNormalChart e x) :
    c.positiveHalf ⊆ (Set.range e)ᶜ := by
  rintro y ⟨hy, hyPos⟩ hyRange
  change 0 < c.normalCoordinate y at hyPos
  rw [(c.normalCoordinate_eq_zero_iff hy).2 hyRange] at hyPos
  exact lt_irrefl 0 hyPos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf_subset_compl_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf_subset_compl_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf_subset_compl_range ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.positiveHalf_subset_compl_range


theorem negativeHalf_subset_compl_range
    (c : EmbeddedSphereNormalChart e x) :
    c.negativeHalf ⊆ (Set.range e)ᶜ := by
  rintro y ⟨hy, hyNeg⟩ hyRange
  change c.normalCoordinate y < 0 at hyNeg
  rw [(c.normalCoordinate_eq_zero_iff hy).2 hyRange] at hyNeg
  exact lt_irrefl 0 hyNeg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf_subset_compl_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf_subset_compl_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf_subset_compl_range ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.negativeHalf_subset_compl_range

theorem neighborhood_eq_halves_union_sphere
    (c : EmbeddedSphereNormalChart e x) :
    c.neighborhood =
      c.positiveHalf ∪ (c.neighborhood ∩ Set.range e) ∪ c.negativeHalf := by
  ext y
  constructor
  · intro hy
    rcases lt_trichotomy (c.normalCoordinate y) 0 with hneg | hzero | hpos
    · exact Or.inr ⟨hy, hneg⟩
    · exact Or.inl (Or.inr ⟨hy, (c.normalCoordinate_eq_zero_iff hy).1 hzero⟩)
    · exact Or.inl (Or.inl ⟨hy, hpos⟩)
  · rintro ((⟨hy, _⟩ | ⟨hy, _⟩) | ⟨hy, _⟩) <;> exact hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_eq_halves_union_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_eq_halves_union_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_eq_halves_union_sphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_eq_halves_union_sphere

theorem neighborhood_diff_range_eq_halves
    (c : EmbeddedSphereNormalChart e x) :
    c.neighborhood \ Set.range e = c.positiveHalf ∪ c.negativeHalf := by
  ext y
  constructor
  · rintro ⟨hy, hyRange⟩
    rcases lt_trichotomy (c.normalCoordinate y) 0 with hneg | hzero | hpos
    · exact Or.inr ⟨hy, hneg⟩
    · exact False.elim
        (hyRange ((c.normalCoordinate_eq_zero_iff hy).1 hzero))
    · exact Or.inl ⟨hy, hpos⟩
  · rintro (⟨hy, hpos⟩ | ⟨hy, hneg⟩)
    · exact ⟨hy, fun hyRange ↦
        (c.positiveHalf_subset_compl_range ⟨hy, hpos⟩) hyRange⟩
    · exact ⟨hy, fun hyRange ↦
        (c.negativeHalf_subset_compl_range ⟨hy, hneg⟩) hyRange⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_diff_range_eq_halves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_diff_range_eq_halves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_diff_range_eq_halves ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.neighborhood_diff_range_eq_halves

theorem subset_positiveHalf_or_subset_negativeHalf
    (c : EmbeddedSphereNormalChart e x) {C : Set N}
    (hC : IsPreconnected C)
    (hCsub : C ⊆ c.neighborhood \ Set.range e) :
    C ⊆ c.positiveHalf ∨ C ⊆ c.negativeHalf := by
  apply hC.subset_or_subset c.isOpen_positiveHalf c.isOpen_negativeHalf
    c.disjoint_positiveHalf_negativeHalf
  rw [← c.neighborhood_diff_range_eq_halves]
  exact hCsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.subset_positiveHalf_or_subset_negativeHalf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.subset_positiveHalf_or_subset_negativeHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.subset_positiveHalf_or_subset_negativeHalf ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.subset_positiveHalf_or_subset_negativeHalf

private theorem isConnected_positiveHalf_of_neighborhood_eq_chart_symm_ball
    (c : EmbeddedSphereNormalChart e x) (ε : ℝ) (hε : 0 < ε)
    (hballTarget : Metric.ball (c.normalForm.codChart (e x)) ε ⊆
      c.normalForm.codChart.target)
    (hneigh : c.neighborhood = c.normalForm.codChart.symm ''
      Metric.ball (c.normalForm.codChart (e x)) ε) :
    IsConnected c.positiveHalf := by
  let h := c.normalForm
  let z₀ : EuclideanThree := h.codChart (e x)
  let ball : Set EuclideanThree := Metric.ball z₀ ε
  let P : Set EuclideanThree := {z | 0 < (h.equiv.symm z).2}
  have hconvP : Convex ℝ P := by
    let normalMap : EuclideanThree →ₗ[ℝ] ℝ :=
      (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
        h.equiv.symm.toLinearEquiv.toLinearMap
    simpa [P, normalMap] using
      convex_halfSpace_gt normalMap.isLinear 0
  have hnonempty : (ball ∩ P).Nonempty := by
    let v : EuclideanThree := h.equiv (0, (1 : ℝ))
    have hvne : v ≠ 0 := by
      intro hv
      have hv' : ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) = 0 :=
        h.equiv.map_eq_zero_iff.mp hv
      have hone := congrArg Prod.snd hv'
      norm_num at hone
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    let δ : ℝ := ε / (2 * ‖v‖)
    have hδ : 0 < δ :=
      div_pos hε (mul_pos (by norm_num) hvnorm)
    let zplus : EuclideanThree := z₀ + δ • v
    have hzball : zplus ∈ ball := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : zplus - z₀ = δ • v := by simp [zplus]
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      change δ * ‖v‖ < ε
      rw [show δ * ‖v‖ = ε / 2 by
        dsimp [δ]
        field_simp]
      linarith
    have hz₀normal : (h.equiv.symm z₀).2 = 0 := by
      exact (c.normalCoordinate_eq_zero_iff
        c.image_mem_neighborhood).2 ⟨x, rfl⟩
    have hzpos : 0 < (h.equiv.symm zplus).2 := by
      simp only [zplus, map_add, map_smul, v,
        h.equiv.symm_apply_apply, Prod.smul_mk, smul_eq_mul,
        mul_one, Prod.snd_add]
      rw [hz₀normal, zero_add]
      exact hδ
    exact ⟨zplus, hzball, hzpos⟩
  have hcoordConnected : IsConnected (ball ∩ P) :=
    ((convex_ball z₀ ε).inter hconvP).isConnected hnonempty
  have himage : c.positiveHalf =
      h.codChart.symm '' (ball ∩ P) := by
    ext y
    constructor
    · rintro ⟨hyO, hyPos⟩
      rw [hneigh] at hyO
      rcases hyO with ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      change 0 <
        (h.equiv.symm (h.codChart (h.codChart.symm z))).2 at hyPos
      rw [h.codChart.right_inv (hballTarget hz)] at hyPos
      exact hyPos
    · rintro ⟨z, ⟨hz, hzPos⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hneigh]
        exact ⟨z, hz, rfl⟩
      · change 0 <
          (h.equiv.symm (h.codChart (h.codChart.symm z))).2
        rw [h.codChart.right_inv (hballTarget hz)]
        exact hzPos
  rw [himage]
  exact hcoordConnected.image _
    (h.codChart.continuousOn_symm.mono
      (inter_subset_left.trans hballTarget))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isConnected_positiveHalf_of_neighborhood_eq_chart_symm_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isConnected_positiveHalf_of_neighborhood_eq_chart_symm_ball target :: scope.openDecls } }

private theorem isConnected_negativeHalf_of_neighborhood_eq_chart_symm_ball
    (c : EmbeddedSphereNormalChart e x) (ε : ℝ) (hε : 0 < ε)
    (hballTarget : Metric.ball (c.normalForm.codChart (e x)) ε ⊆
      c.normalForm.codChart.target)
    (hneigh : c.neighborhood = c.normalForm.codChart.symm ''
      Metric.ball (c.normalForm.codChart (e x)) ε) :
    IsConnected c.negativeHalf := by
  let h := c.normalForm
  let z₀ : EuclideanThree := h.codChart (e x)
  let ball : Set EuclideanThree := Metric.ball z₀ ε
  let P : Set EuclideanThree := {z | (h.equiv.symm z).2 < 0}
  have hconvP : Convex ℝ P := by
    let normalMap : EuclideanThree →ₗ[ℝ] ℝ :=
      (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
        h.equiv.symm.toLinearEquiv.toLinearMap
    simpa [P, normalMap] using
      convex_halfSpace_lt normalMap.isLinear 0
  have hnonempty : (ball ∩ P).Nonempty := by
    let v : EuclideanThree := h.equiv (0, (1 : ℝ))
    have hvne : v ≠ 0 := by
      intro hv
      have hv' : ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) = 0 :=
        h.equiv.map_eq_zero_iff.mp hv
      have hone := congrArg Prod.snd hv'
      norm_num at hone
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    let δ : ℝ := ε / (2 * ‖v‖)
    have hδ : 0 < δ :=
      div_pos hε (mul_pos (by norm_num) hvnorm)
    let zminus : EuclideanThree := z₀ - δ • v
    have hzball : zminus ∈ ball := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : zminus - z₀ = -(δ • v) := by simp [zminus]
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      change δ * ‖v‖ < ε
      rw [show δ * ‖v‖ = ε / 2 by
        dsimp [δ]
        field_simp]
      linarith
    have hz₀normal : (h.equiv.symm z₀).2 = 0 := by
      exact (c.normalCoordinate_eq_zero_iff
        c.image_mem_neighborhood).2 ⟨x, rfl⟩
    have hzneg : (h.equiv.symm zminus).2 < 0 := by
      simp only [zminus, map_sub, map_smul, v,
        h.equiv.symm_apply_apply, Prod.smul_mk, smul_eq_mul,
        mul_one, Prod.snd_sub]
      rw [hz₀normal, zero_sub]
      exact neg_neg_of_pos hδ
    exact ⟨zminus, hzball, hzneg⟩
  have hcoordConnected : IsConnected (ball ∩ P) :=
    ((convex_ball z₀ ε).inter hconvP).isConnected hnonempty
  have himage : c.negativeHalf =
      h.codChart.symm '' (ball ∩ P) := by
    ext y
    constructor
    · rintro ⟨hyO, hyNeg⟩
      rw [hneigh] at hyO
      rcases hyO with ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      change
        (h.equiv.symm (h.codChart (h.codChart.symm z))).2 < 0 at hyNeg
      rw [h.codChart.right_inv (hballTarget hz)] at hyNeg
      exact hyNeg
    · rintro ⟨z, ⟨hz, hzNeg⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hneigh]
        exact ⟨z, hz, rfl⟩
      · change
          (h.equiv.symm (h.codChart (h.codChart.symm z))).2 < 0
        rw [h.codChart.right_inv (hballTarget hz)]
        exact hzNeg
  rw [himage]
  exact hcoordConnected.image _
    (h.codChart.continuousOn_symm.mono
      (inter_subset_left.trans hballTarget))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isConnected_negativeHalf_of_neighborhood_eq_chart_symm_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.EmbeddedSphereNormalChart.isConnected_negativeHalf_of_neighborhood_eq_chart_symm_ball target :: scope.openDecls } }

end EmbeddedSphereNormalChart

theorem exists_embeddedSphereNormalChart_connected_halves
    [ChartedSpace EuclideanThree N] {e : SphereTwo → N}
    (he : Manifold.IsSmoothEmbedding (𝓡 2)
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e)
    (x : SphereTwo) :
    ∃ c : EmbeddedSphereNormalChart e x,
      IsConnected c.positiveHalf ∧ IsConnected c.negativeHalf := by
  let c₀ := Classical.choice (embeddedSphereNormalChart_nonempty he x)
  let h := c₀.normalForm
  let D : Set EuclideanThree := h.codChart '' c₀.neighborhood
  have hDopen : IsOpen D :=
    h.codChart.isOpen_image_of_subset_source c₀.isOpen_neighborhood
      c₀.neighborhood_subset_codChart_source
  have hz₀D : h.codChart (e x) ∈ D :=
    ⟨e x, c₀.image_mem_neighborhood, rfl⟩
  obtain ⟨ε, hε, hballD⟩ := (Metric.isOpen_iff.1 hDopen) _ hz₀D
  let ball : Set EuclideanThree :=
    Metric.ball (h.codChart (e x)) ε
  have hballTarget : ball ⊆ h.codChart.target := by
    intro z hz
    rcases hballD hz with ⟨y, hy, rfl⟩
    exact h.codChart.map_source
      (c₀.neighborhood_subset_codChart_source hy)
  let O : Set N := h.codChart.symm '' ball
  have hOopen : IsOpen O :=
    h.codChart.isOpen_image_symm_of_subset_target
      Metric.isOpen_ball hballTarget
  have hxO : e x ∈ O := by
    refine ⟨h.codChart (e x), Metric.mem_ball_self hε, ?_⟩
    exact h.codChart.left_inv h.mem_codChart_source
  have hOsource : O ⊆ h.codChart.source := by
    rintro y ⟨z, hz, rfl⟩
    exact h.codChart.map_target (hballTarget hz)
  have hOsubset : O ⊆ c₀.neighborhood := by
    rintro y ⟨z, hz, rfl⟩
    rcases hballD hz with ⟨q, hq, hqz⟩
    rw [← hqz, h.codChart.left_inv
      (c₀.neighborhood_subset_codChart_source hq)]
    exact hq
  let c : EmbeddedSphereNormalChart e x := {
    normalForm := h
    neighborhood := O
    isOpen_neighborhood := hOopen
    image_mem_neighborhood := hxO
    neighborhood_subset_codChart_source := hOsource
    tangent_mem_domChart_target := fun y hy ↦
      c₀.tangent_mem_domChart_target y (hOsubset hy)
    neighborhood_inter_range_subset_image := fun _ hy ↦
      c₀.neighborhood_inter_range_subset_image
        ⟨hOsubset hy.1, hy.2⟩
  }
  refine ⟨c, ?_, ?_⟩
  · apply EmbeddedSphereNormalChart.isConnected_positiveHalf_of_neighborhood_eq_chart_symm_ball
      c ε hε
    · simpa [c, ball, h] using hballTarget
    · rfl
  · apply EmbeddedSphereNormalChart.isConnected_negativeHalf_of_neighborhood_eq_chart_symm_ball
      c ε hε
    · simpa [c, ball, h] using hballTarget
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_embeddedSphereNormalChart_connected_halves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_embeddedSphereNormalChart_connected_halves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_embeddedSphereNormalChart_connected_halves ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_embeddedSphereNormalChart_connected_halves

end DifferentialGeometry.Topology.SphereSeparation
