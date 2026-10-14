/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StageTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

def LocallyFinitePLPieceIn.restrict {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y)
    (L : Geometry.SimplicialComplex ℝ E) (hfin : L.faces.Finite)
    (hsub : L.space ⊆ T.complex.space) :
    PLPieceIn E n X (T.map '' L.space) := by
  have : Finite L.faces := hfin.to_subtype
  have hbij : _root_.Set.BijOn T.map L.space (T.map '' L.space) :=
    (T.bijOn.injOn.mono hsub).bijOn_image
  refine ⟨L, hfin, T.map, hbij, T.continuousOn.mono hsub, fun e he => ?_, fun e he => ?_⟩
  · have h := (T.isPiecewiseAffineOn_chart e he).inter_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (T.complex.space ∩ T.map ⁻¹' e.source) ∩ L.space =
        L.space ∩ T.map ⁻¹' e.source := by
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsub hx.1, hx.2⟩, hx.1⟩⟩
    rwa [heq] at h
  · have h := (T.isPiecewiseAffineOn_chart_symm e he).inter_preimage_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (e.target ∩ e.symm ⁻¹' Y) ∩
        (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' L.space =
        e.target ∩ e.symm ⁻¹' (T.map '' L.space) := by
      ext y
      constructor
      · rintro ⟨⟨hy, hyY⟩, hyL⟩
        exact ⟨hy, Function.invFunOn T.map T.complex.space (e.symm y), hyL,
          T.bijOn.invOn_invFunOn.2 hyY⟩
      · rintro ⟨hy, z, hz, hzy⟩
        refine ⟨⟨hy, ?_⟩, ?_⟩
        · change e.symm y ∈ Y
          rw [← hzy]
          exact T.bijOn.mapsTo (hsub hz)
        · change Function.invFunOn T.map T.complex.space (e.symm y) ∈ L.space
          rw [← hzy, T.bijOn.invOn_invFunOn.1 (hsub hz)]
          exact hz
    rw [heq] at h
    refine h.congr fun y hy => ?_
    have hmem := hbij.surjOn.mapsTo_invFunOn hy.2
    have hY := (_root_.Set.image_mono hsub).trans T.bijOn.mapsTo.image_subset hy.2
    exact T.bijOn.injOn (hsub hmem) (T.bijOn.surjOn.mapsTo_invFunOn hY)
      ((hbij.invOn_invFunOn.2 hy.2).trans (T.bijOn.invOn_invFunOn.2 hY).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict

theorem LocallyFinitePLPieceIn.restrict_complex {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) (L : Geometry.SimplicialComplex ℝ E)
    (hfin : L.faces.Finite) (hsub : L.space ⊆ T.complex.space) :
    (T.restrict L hfin hsub).complex = L := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_complex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_complex

theorem LocallyFinitePLPieceIn.restrict_map {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) (L : Geometry.SimplicialComplex ℝ E)
    (hfin : L.faces.Finite) (hsub : L.space ⊆ T.complex.space) :
    (T.restrict L hfin hsub).map = T.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_map ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.restrict_map

theorem PLPieceIn.isPLHomeomorphInto {Y : Set X}
    (T : PLPieceIn (EuclideanSpace ℝ (Fin n)) n X Y) :
    IsPLHomeomorphInto n T.map T.complex.space := by
  have hpa := T.isPolyhedron_space.isPLHomeomorphOn_id.isPiecewiseAffineOn
  have hforward : IsPLOn n n T.map T.complex.space := by
    simpa only [Function.comp_id] using T.isPLOn_comp hpa (_root_.Set.mapsTo_id _)
  have hback : IsPLOn n n (Function.invFunOn T.map T.complex.space) Y := by
    apply T.isPLOn_of_eqOn_comp_invFunOn (isPLOn_iff_isPiecewiseAffineOn.mpr hpa)
    exact fun _ _ => rfl
  refine ⟨hforward, T.bijOn.injOn, fun y hy => ⟨Function.invFunOn T.map T.complex.space,
    ?_, T.bijOn.injOn.leftInvOn_invFunOn⟩⟩
  rw [T.bijOn.image_eq]
  exact hback y (T.bijOn.image_eq ▸ hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphInto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphInto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphInto ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphInto

theorem PLPieceIn.isPLCellOn_image_stdSimplexBoundary
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Y : Set M} (T : PLPieceIn E 3 M Y) {d : ℕ} (hd : d ≤ 3)
    {r : (Fin (d + 1) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin (d + 1))) T.complex.space) :
    IsPLCellOn d Y (T.map '' (r '' stdSimplexBoundary d)) := by
  obtain ⟨_, _, hcell, _⟩ := exists_isPLCellOn_of_le_three d hd
  obtain ⟨P, q, _, hq, _, _, _⟩ := hcell
  let f := r ∘ Function.invFunOn q (stdSimplex ℝ (Fin (d + 1)))
  have hf : IsPLHomeomorphOn f P T.complex.space := hq.symm.trans hr
  obtain ⟨K, hfin, hKP⟩ := (IsPLBall.isPolyhedron ⟨q, hq⟩).exists_simplicialComplex
  have hfK : IsPLHomeomorphOn f K.space T.complex.space := hKP.symm ▸ hf
  let S := T.precomp K hfin hfK
  have hu : IsPLHomeomorphInto 3 (T.map ∘ f) P := by
    have h := S.isPLHomeomorphInto
    change IsPLHomeomorphInto 3 (T.map ∘ f) K.space at h
    rwa [hKP] at h
  refine ⟨P, q, T.map ∘ f, hq, hu, ?_, ?_⟩
  · rw [_root_.Set.image_comp, hf.image_eq, T.bijOn.image_eq]
  · rw [_root_.Set.image_image, _root_.Set.image_image]
    apply EqOn.image_eq
    intro x hx
    change T.map (r x) = T.map (r (Function.invFunOn q _ (q x)))
    rw [hq.bijOn.invOn_invFunOn.1 hx.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLCellOn_image_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLCellOn_image_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLCellOn_image_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLCellOn_image_stdSimplexBoundary

theorem LocallyFinitePLPieceIn.isPLCellOn_image_stdSimplexBoundary
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Y : Set M} (T : LocallyFinitePLPieceIn E 3 M Y)
    (L : Geometry.SimplicialComplex ℝ E) (hfin : L.faces.Finite)
    (hsub : L.space ⊆ T.complex.space) {d : ℕ} (hd : d ≤ 3)
    {r : (Fin (d + 1) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin (d + 1))) L.space) :
    IsPLCellOn d (T.map '' L.space) (T.map '' (r '' stdSimplexBoundary d)) :=
  (T.restrict L hfin hsub).isPLCellOn_image_stdSimplexBoundary hd hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_stdSimplexBoundary

open _root_.Classical in
theorem LocallyFinitePLPieceIn.isPLCellOn_image_boundaryComplex
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Y : Set M} (T : LocallyFinitePLPieceIn E 3 M Y)
    (L : Geometry.SimplicialComplex ℝ E) (hfin : L.faces.Finite)
    (hsub : L.space ⊆ T.complex.space) {d : ℕ} (hd : d ≤ 3)
    (hball : IsPLBall d L.space) :
    IsPLCellOn d (T.map '' L.space) (T.map '' (boundaryComplex d L).space) := by
  let _ : Finite L.faces := hfin.to_subtype
  obtain ⟨r, hr⟩ := hball
  have hcell := T.isPLCellOn_image_stdSimplexBoundary L hfin hsub hd hr
  cases d with
  | zero =>
    have hzero : (boundaryComplex 0 L).space = ∅ := by
      rw [_root_.Set.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨s, hs, _⟩ := (boundaryComplex 0 L).mem_space_iff.mp hx
      obtain ⟨_, t, ht, _, hcard, _⟩ := hs
      have := Finset.card_pos.mpr (L.nonempty_of_mem_faces ht)
      omega
    simpa only [hzero, stdSimplexBoundary_zero, _root_.Set.image_empty] using hcell
  | succ d =>
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hr,
      simplexBoundary_stdVertices_space]
    exact hcell

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_boundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_boundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_boundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_image_boundaryComplex

theorem LocallyFinitePLPieceIn.exists_isPLCellOn_image
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Y : Set M} (T : LocallyFinitePLPieceIn E 3 M Y)
    {P : Set E} (hsub : P ⊆ T.complex.space) {d : ℕ} (hd : d ≤ 3)
    (hball : IsPLBall d P) : ∃ B, IsPLCellOn d (T.map '' P) B := by
  classical
  obtain ⟨L, hfin, hLP⟩ := hball.isPolyhedron.exists_simplicialComplex
  refine ⟨T.map '' (boundaryComplex d L).space, ?_⟩
  have hcell := T.isPLCellOn_image_boundaryComplex L hfin (hLP.symm ▸ hsub) hd
    (hLP.symm ▸ hball)
  rwa [hLP] at hcell

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_isPLCellOn_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_isPLCellOn_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_isPLCellOn_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_isPLCellOn_image

end DifferentialGeometry.Topology.PiecewiseLinear
