import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.mono_of_isOpen {n : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    {f : M → N} {S T : Set M} (hf : IsPLHomeomorphInto n f S)
    (hT : IsOpen T) (hTS : T ⊆ S) : IsPLHomeomorphInto n f T := by
  have hopen : IsOpen (f '' T) :=
    DifferentialGeometry.Topology.isOpen_image_of_continuousOn_injOn
      (E := EuclideanSpace ℝ (Fin n)) hT (hf.continuousOn.mono hTS) (hf.injOn.mono hTS)
  refine ⟨hf.isPLOn.mono_of_isOpen hT hTS, hf.injOn.mono hTS, ?_⟩
  intro y hy
  obtain ⟨g, hg, hleft⟩ := hf.2.2 y (_root_.Set.image_mono hTS hy)
  exact ⟨g, hg.mono_of_mem_nhdsWithin (_root_.Set.image_mono hTS)
    (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hy)), hleft.mono hTS⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isOpen ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isOpen

theorem IsPLHomeomorphInto.image_frontier_of_isCompact_subset_interior
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P D : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hD : IsCompact D) (hDP : D ⊆ interior P) :
    u '' frontier D = frontier (u '' D) :=
  (hu.mono_of_isOpen isOpen_interior interior_subset).image_frontier isOpen_interior hD hDP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_frontier_of_isCompact_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_frontier_of_isCompact_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_frontier_of_isCompact_subset_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_frontier_of_isCompact_subset_interior

theorem IsPLHomeomorphInto.invFunOn_region_topology
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) {N : Set M} (hN : IsCompact N)
    (hNP : N ⊆ interior (u '' P)) :
    IsCompact (Function.invFunOn u P '' N) ∧
      Function.invFunOn u P '' N ⊆ interior P ∧
      u '' (Function.invFunOn u P '' N) = N ∧
      u '' frontier (Function.invFunOn u P '' N) = frontier N ∧
      u '' interior (Function.invFunOn u P '' N) = interior N := by
  have hsub := hNP.trans interior_subset
  have hinv := hu.injOn.leftInvOn_invFunOn
  have hcont : ContinuousOn (Function.invFunOn u P) (u '' P) :=
    fun x hx => (hu.isPLOn_inverse hinv x hx).continuousWithinAt
  have hcompact := hN.image_of_continuousOn (hcont.mono hsub)
  have hint : Function.invFunOn u P '' N ⊆ interior P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hu.image_interior.symm.subset (hNP hx)
    rw [hinv (interior_subset hy)]
    exact hy
  have himage : u '' (Function.invFunOn u P '' N) = N := by
    rw [_root_.Set.image_image]
    exact (_root_.Set.image_congr fun x hx =>
      hu.injOn.bijOn_image.invOn_invFunOn.2 (hsub hx)).trans (_root_.Set.image_id' N)
  have hfront : u '' frontier (Function.invFunOn u P '' N) = frontier N := by
    rw [hu.image_frontier_of_isCompact_subset_interior hcompact hint, himage]
  refine ⟨hcompact, hint, himage, hfront, ?_⟩
  rw [← self_sdiff_frontier (s := Function.invFunOn u P '' N),
    (hu.injOn.mono (hint.trans interior_subset)).image_sdiff_subset
      hcompact.isClosed.frontier_subset,
    himage, hfront, self_sdiff_frontier]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_region_topology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_region_topology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_region_topology ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn_region_topology

theorem IsPLHomeomorphInto.image_interior_of_isCompact_subset_interior
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P D : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hD : IsCompact D) (hDP : D ⊆ interior P) :
    u '' interior D = interior (u '' D) := by
  rw [← self_sdiff_frontier (s := D),
    (hu.injOn.mono (hDP.trans interior_subset)).image_sdiff_subset hD.isClosed.frontier_subset,
    hu.image_frontier_of_isCompact_subset_interior hD hDP, self_sdiff_frontier]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_interior_of_isCompact_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_interior_of_isCompact_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_interior_of_isCompact_subset_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.image_interior_of_isCompact_subset_interior

end DifferentialGeometry.Topology.PiecewiseLinear
