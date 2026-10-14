import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Topology.Connected.OpenPartition
import Submission.DifferentialGeometry.Topology.Embedding.LocalSeparation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
import Submission.DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M} {U : Set M}

omit [SigmaCompactSpace M] in
theorem LocalCap.outer_boundary_isSmoothEmbedding (cap : LocalCap S eps x t U) :
    Manifold.IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => cap.tube_map (z, 1)) := by
  let f : Sphere 2 → Cylinder := fun z => (z, 1)
  have hf : Manifold.IsSmoothEmbedding I2 IC ∞ f :=
    (Manifold.IsSmoothEmbedding.id : Manifold.IsSmoothEmbedding I2 I2 ∞ (Prod.fst ∘ f)).of_comp
      (J := IC) (by simp) (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hsrc (z : Sphere 2) : f z ∈ cap.tube_map.source :=
    cap.tube_domain ⟨mem_univ _, zero_le_one, le_rfl⟩
  have hcont : ContMDiff I2 I3 ∞ (cap.tube_map ∘ f) :=
    contMDiffOn_univ.mp (cap.tube_map.contMDiffOn_toFun.comp hf.contMDiff.contMDiffOn
      (fun z _ => hsrc z))
  have hinj : Function.Injective (cap.tube_map ∘ f) := by
    intro a b hab
    exact congrArg Prod.fst (cap.tube_map.toPartialEquiv.injOn (hsrc a) (hsrc b) hab)
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hcont ?_,
    (hcont.continuous.isClosedEmbedding hinj).isEmbedding⟩
  intro z
  change Function.Injective (mfderiv I2 I3 (cap.tube_map ∘ f) z)
  have hlocal := cap.tube_map.isLocalDiffeomorphAt IC I3 ∞ (hsrc z)
  rw [mfderiv_comp z (hlocal.contMDiffAt.mdifferentiableAt (by simp))
    (hf.contMDiff.mdifferentiable (by simp) z)]
  exact (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    ((hf.isImmersion.isImmersionAt z).injective_mfderiv (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.outer_boundary_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.outer_boundary_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.outer_boundary_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.outer_boundary_isSmoothEmbedding

omit [T2Space M] [SigmaCompactSpace M] in
theorem LocalCap.range_outer_boundary_eq (cap : LocalCap S eps x t U) :
    range (fun z : Sphere 2 => cap.tube_map (z, 1)) = frontier U := by
  rw [← cap.outer_boundary]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z, 1), ⟨mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨⟨z, s⟩, hs, rfl⟩
    have hs1 : s = 1 := hs.2
    rw [hs1]
    exact _root_.Set.mem_range_self z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.range_outer_boundary_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.range_outer_boundary_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.range_outer_boundary_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.range_outer_boundary_eq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M} {U : Set M}

omit [SigmaCompactSpace M] in
theorem LocalCap.isConnected_interior_and_compl [PreconnectedSpace M]
    (cap : LocalCap S eps x t U) : IsConnected (interior U) ∧ IsConnected Uᶜ := by
  let _ : ConnectedSpace (Sphere 2) := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  have hc : IsClosed U := cap.isCompact_carrier.isClosed
  have hi : (interior U).Nonempty := ⟨x, cap.core_inside (interior_subset cap.center_inside)⟩
  have hfront : (frontier U).Nonempty := by
    let p : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    refine ⟨cap.tube_map (p, 1), ?_⟩
    rw [← cap.outer_boundary]
    exact ⟨(p, 1), ⟨mem_univ _, rfl⟩, rfl⟩
  have hext : Uᶜ.Nonempty := by
    by_contra h
    have hU : U = univ := _root_.Set.eq_univ_of_forall fun y => by
      by_contra hy
      exact h ⟨y, hy⟩
    simp only [hU, frontier_univ, Set.not_nonempty_empty] at hfront
  have hcover : interior U ∪ Uᶜ = (frontier U)ᶜ := by
    rw [compl_frontier_eq_union_interior, hc.isOpen_compl.interior_eq]
  have hcard : ENat.card (ConnectedComponents ↥(interior U ∪ Uᶜ)) ≤ 2 := by
    rw [hcover, ← cap.range_outer_boundary_eq]
    exact cap.outer_boundary_isSmoothEmbedding.card_connectedComponents_compl_le_two_of_compact
      (by simp [ThreeSpace])
  exact DifferentialGeometry.Topology.isConnected_open_partition_of_card_connectedComponents_le_two
    isOpen_interior hc.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hi hext hcard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.isConnected_interior_and_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.isConnected_interior_and_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.isConnected_interior_and_compl ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.isConnected_interior_and_compl

omit [SigmaCompactSpace M] in
theorem LocalCap.complementary_region [PreconnectedSpace M] [CompactSpace M]
    (cap : LocalCap S eps x t U) :
    IsOpen Uᶜ ∧ IsConnected Uᶜ ∧ IsCompact (closure Uᶜ) ∧
      IsConnected (closure Uᶜ) ∧ closure Uᶜ = (interior U)ᶜ ∧
      frontier Uᶜ = frontier U ∧ U ∪ closure Uᶜ = _root_.Set.univ ∧ U ∩ closure Uᶜ = frontier U ∧
      _root_.Set.range (fun z : Sphere 2 => cap.tube_map (z, 1)) = frontier Uᶜ ∧
      Manifold.IsSmoothEmbedding I2 I3 ∞ (fun z : Sphere 2 => cap.tube_map (z, 1)) := by
  have hc : IsClosed U := cap.isCompact_carrier.isClosed
  have hext := cap.isConnected_interior_and_compl.2
  refine ⟨hc.isOpen_compl, hext, isClosed_closure.isCompact, hext.closure,
    closure_compl, frontier_compl U, ?_, ?_, ?_, cap.outer_boundary_isSmoothEmbedding⟩
  · rw [closure_compl]
    apply _root_.Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ U
    · exact Or.inl hy
    · exact Or.inr fun h => hy (interior_subset h)
  · rw [closure_compl, hc.frontier_eq]
    rfl
  · rw [frontier_compl]
    exact cap.range_outer_boundary_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.complementary_region then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.complementary_region"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.complementary_region ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.complementary_region

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M} {U : Set M}

theorem LocalCap.interior_closure_compl (cap : LocalCap S eps x t U) :
    interior (closure Uᶜ) = Uᶜ := by
  obtain ⟨K, hK, _hx⟩ := cap.exists_compactDomain
  rw [closure_compl, interior_compl]
  exact congrArg _root_.Compl.compl (by simpa only [hK] using K.regular_closed)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.interior_closure_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.interior_closure_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.interior_closure_compl ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.interior_closure_compl

theorem LocalCap.frontier_closure_compl (cap : LocalCap S eps x t U) :
    frontier (closure Uᶜ) = frontier U := by
  have hc : IsClosed U := cap.isCompact_carrier.isClosed
  calc
    frontier (closure Uᶜ) = closure Uᶜ \ Uᶜ := by
      rw [frontier, closure_closure, cap.interior_closure_compl]
    _ = frontier Uᶜ := by rw [frontier, hc.isOpen_compl.interior_eq]
    _ = frontier U := frontier_compl U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.frontier_closure_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.frontier_closure_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.frontier_closure_compl ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.frontier_closure_compl

theorem LocalCap.nonempty_smoothSideClosure_compl (cap : LocalCap S eps x t U) :
    Nonempty (SmoothSideClosure Uᶜ (frontier U)) := by
  obtain ⟨K, hK, _hx⟩ := cap.exists_compactDomain
  have hregular : closure (interior U) = U := by
    simpa only [hK] using K.regular_closed
  have hc : IsClosed U := cap.isCompact_carrier.isClosed
  let e : Sphere 2 → M := fun z => cap.tube_map (z, 1)
  have he : Manifold.IsSmoothEmbedding I2 I3 ∞ e := cap.outer_boundary_isSmoothEmbedding
  have hrange : _root_.Set.range e = frontier U := cap.range_outer_boundary_eq
  have hBclosure : closure Uᶜ = Uᶜ ∪ _root_.Set.range e := by
    rw [hrange, ← frontier_compl U]
    exact closure_eq_self_union_frontier _
  have hCclosure : closure (interior U) = interior U ∪ _root_.Set.range e := by
    rw [hregular, hrange, ← closure_eq_interior_union_frontier, hc.closure_eq]
  have hnormal (z : Sphere 2) : Nonempty (EmbeddedSphereSideNormalChart e Uᶜ z) := by
    apply exists_embeddedSphereSideNormalChart_of_isOpen_side he hc.isOpen_compl isOpen_interior
      ?_ ?_ ?_ hBclosure hCclosure z
    · rw [hrange]
      exact compl_subset_compl.mpr (hc.frontier_subset)
    · exact (disjoint_compl_right.mono_left interior_subset).symm
    · rw [hrange, compl_frontier_eq_union_interior, hc.isOpen_compl.interior_eq, _root_.Set.union_comm]
  have hresult : Nonempty (SmoothSideClosure Uᶜ (_root_.Set.range e)) :=
    ⟨smoothSideClosure hc.isOpen_compl hBclosure hnormal⟩
  rwa [hrange] at hresult

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.nonempty_smoothSideClosure_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.nonempty_smoothSideClosure_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.nonempty_smoothSideClosure_compl ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.nonempty_smoothSideClosure_compl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
