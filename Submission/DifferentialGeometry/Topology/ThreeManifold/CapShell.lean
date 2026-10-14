import Submission.DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import Submission.DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.CollarReparametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

local instance _root_.Submission.DifferentialGeometry.Topology.SphericalCapping.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd ``Submission.DifferentialGeometry.Topology.SphericalCapping.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def capShellMap (b : T.Boundary) (q : S2 × ℝ) : N.Carrier :=
  (C.capBallChart b).chart (q.2 • (q.1 : E3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capShellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capShellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capShellMap ``Submission.DifferentialGeometry.Topology.SphericalCapping.capShellMap

private theorem norm_radial (q : S2 × ℝ) (hq : 0 < q.2) :
    ‖q.2 • (q.1 : E3)‖ = q.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.norm_radial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.norm_radial target :: scope.openDecls } }

private theorem radial_mem_capBallChart_source (b : T.Boundary) (q : S2 × ℝ)
    (hq : q.2 ∈ _root_.Set.Ioo (0 : ℝ) 4) : q.2 • (q.1 : E3) ∈ (C.capBallChart b).chart.source := by
  rw [C.capBallChart_source, mem_ball_zero_iff, norm_radial q hq.1]
  exact hq.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.radial_mem_capBallChart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.radial_mem_capBallChart_source target :: scope.openDecls } }

theorem isLocalDiffeomorphAt_capShellMap (b : T.Boundary) (q : S2 × ℝ)
    (hq : q.2 ∈ _root_.Set.Ioo (0 : ℝ) 4) :
    IsLocalDiffeomorphAt CI (𝓡 3) ∞ (C.capShellMap b) q :=
  Manifold.isLocalDiffeomorphAt_chart_sphere_smul (C.capBallChart b).chart q hq.1
    (C.radial_mem_capBallChart_source b q hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capShellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capShellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capShellMap ``Submission.DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capShellMap

theorem capShellMap_injOn (b : T.Boundary) :
    InjOn (C.capShellMap b) (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 4) := by
  intro p hp q hq h
  have heq := (C.capBallChart b).chart.injOn
    (C.radial_mem_capBallChart_source b p hp.2) (C.radial_mem_capBallChart_source b q hq.2) h
  have hrad : p.2 = q.2 := by
    have hn := congrArg _root_.Norm.norm heq
    rwa [norm_radial p hp.2.1, norm_radial q hq.2.1] at hn
  apply Prod.ext
  · apply Subtype.ext
    apply (smul_right_injective E3 (ne_of_gt hp.2.1))
    rwa [← hrad] at heq
  · exact hrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capShellMap_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capShellMap_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capShellMap_injOn ``Submission.DifferentialGeometry.Topology.SphericalCapping.capShellMap_injOn

private theorem norm_cap_radial_lt_one (b : T.Boundary) (q : S2 × ℝ)
    (hq : q.2 ∈ _root_.Set.Ioo (0 : ℝ) 4) :
    ‖(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • (q.2 • (q.1 : E3))‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs, norm_radial q hq.1]
  have h : |if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)| = 1 / 4 := by cases b.2 <;> norm_num
  rw [h]
  linarith [hq.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.norm_cap_radial_lt_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.norm_cap_radial_lt_one target :: scope.openDecls } }

theorem capShellMap_eq_cap (b : T.Boundary) (q : S2 × ℝ) (hq : q.2 ∈ _root_.Set.Ioo (0 : ℝ) 4) :
    C.capShellMap b q = C.cap b
      ⟨(if b.2 then (1 / 4 : ℝ) else -(1 / 4 : ℝ)) • (q.2 • (q.1 : E3)),
        (norm_cap_radial_lt_one b q hq).le⟩ :=
  C.capBallChart_apply b _ (norm_cap_radial_lt_one b q hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capShellMap_eq_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capShellMap_eq_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capShellMap_eq_cap ``Submission.DifferentialGeometry.Topology.SphericalCapping.capShellMap_eq_cap

@[simp] theorem capShellMap_one (b : T.Boundary) (z : S2) :
    C.capShellMap b (z, 1) = ((C.capBallChart b).toBallChart.boundaryMap z).val := by
  simp only [capShellMap, one_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capShellMap_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capShellMap_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capShellMap_one ``Submission.DifferentialGeometry.Topology.SphericalCapping.capShellMap_one

theorem exists_capShell_partialDiffeomorph (b : T.Boundary) :
    ∃ e : PartialDiffeomorph CI (𝓡 3) (S2 × ℝ) N.Carrier ∞,
      e.source = _root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 4 ∧
      e.target = C.capShellMap b '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 4) ∧
      (e : S2 × ℝ → N.Carrier) = C.capShellMap b := by
  let _ : Nonempty S2 := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  exact Manifold.exists_partialDiffeomorph_of_injOn (isOpen_univ.prod isOpen_Ioo)
    (fun q => C.isLocalDiffeomorphAt_capShellMap b q.val q.property.2) (C.capShellMap_injOn b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.exists_capShell_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.exists_capShell_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.exists_capShell_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.SphericalCapping.exists_capShell_partialDiffeomorph

theorem capShellMap_image_subset_cap_interior (b : T.Boundary) :
    C.capShellMap b '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 4) ⊆
      C.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1} := by
  rintro y ⟨q, hq, rfl⟩
  rw [← C.capBallChart_target]
  exact (C.capBallChart b).chart.map_source (C.radial_mem_capBallChart_source b q hq.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capShellMap_image_subset_cap_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capShellMap_image_subset_cap_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capShellMap_image_subset_cap_interior ``Submission.DifferentialGeometry.Topology.SphericalCapping.capShellMap_image_subset_cap_interior

theorem disjoint_capShellMap_image_core (b : T.Boundary) :
    Disjoint (C.capShellMap b '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 4)) (_root_.Set.range C.coreInclusion) := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
  apply Set.disjoint_left.mpr
  intro y hy hcore
  obtain ⟨p, hp, rfl⟩ := C.capShellMap_image_subset_cap_interior b hy
  have hboth : C.cap b p ∈ _root_.Set.range C.coreInclusion ∩ _root_.Set.range (C.cap b) := ⟨hcore, ⟨p, rfl⟩⟩
  rw [C.core_cap_intersection b] at hboth
  obtain ⟨z, hz⟩ := hboth
  have hcap : C.cap b (sphereToClosedCell ((C.attaching b).symm z)) = C.cap b p := by
    rw [C.boundary_eq b ((C.attaching b).symm z), Diffeomorph.apply_symm_apply]
    exact hz
  have heq := congrArg (fun q : ClosedCell 3 => ‖q.val‖) ((C.cap_embedding b).isEmbedding.injective hcap)
  have hz1 : ‖(sphereToClosedCell ((C.attaching b).symm z)).val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ((C.attaching b).symm z).property
  rw [hz1] at heq
  exact (ne_of_lt hp) heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.disjoint_capShellMap_image_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.disjoint_capShellMap_image_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.disjoint_capShellMap_image_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.disjoint_capShellMap_image_core

theorem exists_capShell_reparametrization (b : T.Boundary) (r₀ r₁ : ℝ)
    (hr₀ : r₀ ∈ _root_.Set.Ioo (0 : ℝ) 4) (hr₁ : r₁ ∈ _root_.Set.Ioo (0 : ℝ) 4) :
    ∃ (φ : ℝ ≃ₘ[ℝ] ℝ) (F : N.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier),
      φ r₀ = r₁ ∧ (∀ r, 0 < deriv φ r) ∧
      (∀ z r, r ∈ _root_.Set.Ioo (0 : ℝ) 4 → F (C.capShellMap b (z, r)) = C.capShellMap b (z, φ r)) ∧
      (∀ z r, r ∈ _root_.Set.Ioo (0 : ℝ) 4 → F.symm (C.capShellMap b (z, r)) =
        C.capShellMap b (z, φ.symm r)) ∧
      (∀ x : T.core, F (C.coreInclusion x) = C.coreInclusion x ∧
        F.symm (C.coreInclusion x) = C.coreInclusion x) ∧
      (∀ b' : T.Boundary, b' ≠ b → ∀ x : ClosedCell 3,
        F (C.cap b' x) = C.cap b' x ∧ F.symm (C.cap b' x) = C.cap b' x) ∧
      ∃ K : Set N.Carrier, IsCompact K ∧ K ⊆ C.capShellMap b '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 4) ∧
        ∀ x, x ∉ K → F x = x ∧ F.symm x = x := by
  obtain ⟨e, hs, ht, he⟩ := C.exists_capShell_partialDiffeomorph b
  obtain ⟨φ, _, _, _, hmove, hpos, _, F, _, _, _, hF, hFi, K, hK, hKe, hfix⟩ :=
    e.exists_collar_reparametrization_isotopy hr₀ hr₁ (by rw [hs])
  have hKsub : K ⊆ C.capShellMap b '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) 4) := by
    simpa only [he] using hKe
  have hfix' (x : N.Carrier) (hx : x ∉ K) : F 1 x = x ∧ (F 1).symm x = x :=
    ⟨(hfix 1).1 hx, (hfix 1).2 hx⟩
  refine ⟨φ 1, F 1, ?_, hpos 1, ?_, ?_, ?_, ?_, K, hK, hKsub, hfix'⟩
  · have h := hmove 1 ⟨zero_le_one, le_rfl⟩
    simpa using h
  · intro z r hr
    have h := hF 1 (z, r) (hs ▸ ⟨mem_univ _, hr⟩)
    simpa only [he] using h
  · intro z r hr
    have h := hFi 1 (z, r) (hs ▸ ⟨mem_univ _, hr⟩)
    simpa only [he] using h
  · intro x
    apply hfix'
    intro hx
    exact Set.disjoint_left.mp (C.disjoint_capShellMap_image_core b) (hKsub hx) ⟨x, rfl⟩
  · intro b' hne x
    apply hfix'
    intro hx
    obtain ⟨y, _, hy⟩ := C.capShellMap_image_subset_cap_interior b (hKsub hx)
    exact Set.disjoint_left.mp (C.cap_disjoint hne.symm) ⟨y, hy⟩ ⟨x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.exists_capShell_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.exists_capShell_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.exists_capShell_reparametrization ``Submission.DifferentialGeometry.Topology.SphericalCapping.exists_capShell_reparametrization

end DifferentialGeometry.Topology.SphericalCapping
