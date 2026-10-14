import Submission.DifferentialGeometry.Topology.ThreeManifold.CapAnnulus
import Submission.DifferentialGeometry.Topology.ThreeManifold.CoreCapOppositeSides
import Submission.DifferentialGeometry.Topology.Attachment.Union

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Annulus" => Sphere × _root_.Set.Icc (1 / 4 : ℝ) 1
private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.cellCharts
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.cellCharts target :: scope.openDecls } }
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.cellSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.cellSmooth target :: scope.openDecls } }

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def capAnnuliBoundaryInclusion : (Σ _b : T.Boundary, Sphere) → (Σ _b : T.Boundary, Annulus) :=
  fun q => ⟨q.1, q.2, ⟨1, by norm_num⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliBoundaryInclusion ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliBoundaryInclusion

def capAnnuliMap (q : Σ _b : T.Boundary, Annulus) : N.Carrier := C.capAnnulusMap q.1 q.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap

def capAnnuliAttachingMap (q : Σ _b : T.Boundary, Sphere) : _root_.Set.range C.coreInclusion :=
  ⟨C.coreInclusion (T.coreBoundarySphere q.1 (C.attaching q.1 q.2)), ⟨_, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap

theorem capAnnuliAttachingMap_val (q : Σ _b : T.Boundary, Sphere) :
    (C.capAnnuliAttachingMap q).val = C.capAnnuliMap (capAnnuliBoundaryInclusion q) :=
  (C.capAnnulusMap_outer q.1 q.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap_val ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliAttachingMap_val

theorem capAnnuliMap_continuous : Continuous C.capAnnuliMap :=
  continuous_sigma fun b => (C.capAnnulusMap b).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_continuous ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_continuous

theorem capAnnuliMap_injective : _root_.Function.Injective C.capAnnuliMap := by
  rintro ⟨b, p⟩ ⟨b', q⟩ h
  have hbb : b = b' := by
    by_contra hne
    have hp : C.capAnnulusMap b p ∈ _root_.Set.range (C.cap b) := by
      have h := _root_.Set.mem_range_self p (f := C.capAnnulusMap b)
      rw [C.range_capAnnulusMap b] at h
      exact ⟨h.choose, h.choose_spec.2⟩
    have hq : C.capAnnulusMap b' q ∈ _root_.Set.range (C.cap b') := by
      have h := _root_.Set.mem_range_self q (f := C.capAnnulusMap b')
      rw [C.range_capAnnulusMap b'] at h
      exact ⟨h.choose, h.choose_spec.2⟩
    have heq : C.capAnnulusMap b p = C.capAnnulusMap b' q := h
    exact Set.disjoint_left.mp (C.cap_disjoint hne) hp (heq.symm ▸ hq)
  subst b'
  have hpq : p = q := C.capAnnulusMap_injective b h
  subst q
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_injective ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_injective

theorem range_capAnnuliMap : _root_.Set.range C.capAnnuliMap = ⋃ b, _root_.Set.range (C.capAnnulusMap b) := by
  ext y
  simp only [_root_.Set.mem_range, _root_.Set.mem_iUnion]
  exact ⟨fun ⟨⟨b, q⟩, h⟩ => ⟨b, q, h⟩, fun ⟨b, q, h⟩ => ⟨⟨b, q⟩, h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.range_capAnnuliMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.range_capAnnuliMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.range_capAnnuliMap ``Submission.DifferentialGeometry.Topology.SphericalCapping.range_capAnnuliMap

private theorem capAnnulusMap_mem_core_iff (b : T.Boundary) (q : Annulus) :
    C.capAnnulusMap b q ∈ _root_.Set.range C.coreInclusion ↔ q.2.val = 1 := by
  constructor
  · intro h
    let x : ClosedCell 3 := ⟨q.2.val • q.1.val, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [q.2.property.1]),
        norm_eq_of_mem_sphere, mul_one]
      exact q.2.property.2⟩
    have hx : C.cap b x ∈ _root_.Set.range C.coreInclusion := h
    obtain ⟨z, hz⟩ := C.eq_sphereToClosedCell_of_cap_mem_coreImage b hx
    have hn := congrArg (fun w : ClosedCell 3 => ‖w.val‖) hz
    change ‖z.val‖ = ‖q.2.val • q.1.val‖ at hn
    rw [norm_eq_of_mem_sphere, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [q.2.property.1]), norm_eq_of_mem_sphere, mul_one] at hn
    exact hn.symm
  · intro h
    have ht : q.2 = (⟨1, by norm_num⟩ : _root_.Set.Icc (1 / 4 : ℝ) 1) := Subtype.ext h
    have hq : q = (q.1, ⟨1, by norm_num⟩) := Prod.ext rfl ht
    rw [hq, C.capAnnulusMap_outer]
    exact _root_.Set.mem_range_self _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnulusMap_mem_core_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capAnnulusMap_mem_core_iff target :: scope.openDecls } }

private theorem capAnnuliMap_mem_core_boundary (q : Σ _b : T.Boundary, Annulus)
    (hq : C.capAnnuliMap q ∈ _root_.Set.range C.coreInclusion) : q ∈ _root_.Set.range (capAnnuliBoundaryInclusion (T := T)) := by
  have ht := (C.capAnnulusMap_mem_core_iff q.1 q.2).mp hq
  refine ⟨⟨q.1, q.2.1⟩, ?_⟩
  cases q with
  | mk b p =>
    have he : (p.1, (⟨1, by norm_num⟩ : _root_.Set.Icc (1 / 4 : ℝ) 1)) = p :=
      Prod.ext rfl (Subtype.ext ht.symm)
    exact congrArg (fun r : Annulus => (⟨b, r⟩ : Σ _b : T.Boundary, Annulus)) he

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_mem_core_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capAnnuliMap_mem_core_boundary target :: scope.openDecls } }

private theorem isClosed_coreImage : IsClosed (_root_.Set.range C.coreInclusion) := by
  have hi : IsCompact (_root_.Set.range C.coreInclusion) := by
    let _ : CompactSpace T.core := isCompact_iff_compactSpace.mp C.core_compact
    exact isCompact_range C.coreInclusion.continuous
  exact hi.isClosed

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.isClosed_coreImage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.isClosed_coreImage target :: scope.openDecls } }

abbrev PuncturedCapping :=
  AdjunctionSpace (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.PuncturedCapping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.PuncturedCapping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.PuncturedCapping ``Submission.DifferentialGeometry.Topology.SphericalCapping.PuncturedCapping

def capAnnuliHomeomorph : C.PuncturedCapping ≃ₜ
    (_root_.Set.range C.coreInclusion ∪ ⋃ b, _root_.Set.range (C.capAnnulusMap b) : Set N.Carrier) :=
  (adjunctionHomeomorphUnionImage (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
    C.capAnnuliMap C.capAnnuliAttachingMap_val C.capAnnuliMap_injective C.capAnnuliMap_continuous
    C.capAnnuliMap_mem_core_boundary C.isClosed_coreImage).trans
      (Homeomorph.setCongr (by rw [C.range_capAnnuliMap]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph

@[simp] theorem capAnnuliHomeomorph_core (x : _root_.Set.range C.coreInclusion) :
    (C.capAnnuliHomeomorph (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap x)).val = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_core

@[simp] theorem capAnnuliHomeomorph_annulus (b : T.Boundary) (q : Annulus) :
    (C.capAnnuliHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap ⟨b, q⟩)).val = C.capAnnulusMap b q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_annulus ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliHomeomorph_annulus

theorem capBallChart_image_ball (b : T.Boundary) :
    (C.capBallChart b).chart '' Metric.ball (0 : E3) 1 =
      C.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1 / 4} := by
  let r : ℝ := if b.2 then 1 / 4 else -(1 / 4)
  have habs : |r| = 1 / 4 := by dsimp only [r]; cases b.2 <;> norm_num
  have hnorm (x : E3) : ‖r • x‖ = (1 / 4 : ℝ) * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, habs]
  have hr : r ≠ 0 := by intro h; rw [h, abs_zero] at habs; norm_num at habs
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hsmall : ‖r • x‖ < 1 / 4 := by
      rw [hnorm]
      have h := mem_ball_zero_iff.mp hx
      linarith
    refine ⟨⟨r • x, by linarith⟩, hsmall, ?_⟩
    exact (C.capBallChart_apply b x (by change ‖r • x‖ < 1; linarith)).symm
  · rintro ⟨x, hx, rfl⟩
    change ‖x.val‖ < 1 / 4 at hx
    let v : E3 := r⁻¹ • x.val
    have hv : r • v = x.val := by simp [v, smul_smul, hr]
    have hvnorm : ‖v‖ < 1 := by
      have h := hnorm v
      rw [hv] at h
      change ‖x.val‖ < 1 / 4 at hx
      linarith
    refine ⟨v, mem_ball_zero_iff.mpr hvnorm, ?_⟩
    rw [C.capBallChart_apply b v (by change ‖r • v‖ < 1; rw [hv]; linarith)]
    apply congrArg (C.cap b)
    exact Subtype.ext hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capBallChart_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capBallChart_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capBallChart_image_ball ``Submission.DifferentialGeometry.Topology.SphericalCapping.capBallChart_image_ball

theorem core_union_capAnnuli_eq_compl_capBallChart :
    _root_.Set.range C.coreInclusion ∪ ⋃ b, _root_.Set.range (C.capAnnulusMap b) =
      (⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ := by
  simp_rw [C.capBallChart_image_ball]
  ext y
  constructor
  · intro hy hsmall
    obtain ⟨b, x, hx, hxy⟩ := Set.mem_iUnion.mp hsmall
    rcases hy with hcore | hann
    · have hcore' : C.cap b x ∈ _root_.Set.range C.coreInclusion := hxy.symm ▸ hcore
      obtain ⟨z, hz⟩ := C.eq_sphereToClosedCell_of_cap_mem_coreImage b hcore'
      have hn := congrArg (fun w : ClosedCell 3 => ‖w.val‖) hz
      change ‖z.val‖ = ‖x.val‖ at hn
      rw [norm_eq_of_mem_sphere] at hn
      change ‖x.val‖ < 1 / 4 at hx
      linarith
    · obtain ⟨b', hb'⟩ := mem_iUnion.mp hann
      rw [C.range_capAnnulusMap] at hb'
      obtain ⟨x', hx', hx'y⟩ := hb'
      by_cases hbb : b = b'
      · subst b'
        have heq := (C.cap_embedding b).isEmbedding.injective (hxy.trans hx'y.symm)
        rw [heq] at hx
        exact not_lt_of_ge (show 1 / 4 ≤ ‖x'.val‖ from hx') (show ‖x'.val‖ < 1 / 4 from hx)
      · exact Set.disjoint_left.mp (C.cap_disjoint hbb) ⟨x, hxy⟩ ⟨x', hx'y⟩
  · intro hy
    have hex : y ∈ _root_.Set.range C.coreInclusion ∪ ⋃ b, _root_.Set.range (C.cap b) := by rw [C.exhaustive]; trivial
    rcases hex with h | h
    · exact Or.inl h
    · obtain ⟨b, x, hx⟩ := mem_iUnion.mp h
      refine Or.inr (mem_iUnion.mpr ⟨b, ?_⟩)
      rw [C.range_capAnnulusMap]
      refine ⟨x, ?_, hx⟩
      change 1 / 4 ≤ ‖x.val‖
      apply le_of_not_gt
      intro hsmall
      exact hy (mem_iUnion.mpr ⟨b, x, hsmall, hx⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.core_union_capAnnuli_eq_compl_capBallChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.core_union_capAnnuli_eq_compl_capBallChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.core_union_capAnnuli_eq_compl_capBallChart ``Submission.DifferentialGeometry.Topology.SphericalCapping.core_union_capAnnuli_eq_compl_capBallChart

def puncturedCappingHomeomorph : C.PuncturedCapping ≃ₜ
    ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier) :=
  C.capAnnuliHomeomorph.trans (Homeomorph.setCongr C.core_union_capAnnuli_eq_compl_capBallChart)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph

@[simp] theorem puncturedCappingHomeomorph_core (x : _root_.Set.range C.coreInclusion) :
    (C.puncturedCappingHomeomorph (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap x)).val = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_core

@[simp] theorem puncturedCappingHomeomorph_annulus (b : T.Boundary) (q : Annulus) :
    (C.puncturedCappingHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap ⟨b, q⟩)).val = C.capAnnulusMap b q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_annulus ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingHomeomorph_annulus

end DifferentialGeometry.Topology.SphericalCapping
