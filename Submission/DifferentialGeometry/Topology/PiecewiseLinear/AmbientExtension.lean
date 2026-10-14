/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem exists_piecewiseAffine_lipschitz_extension_of_eq_zero_on_faces [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, _root_.Set.EqOn f A (convexHull ℝ (s : Set E)))
    {N : Set E} (hN : IsPolyhedron N) (hzero : _root_.Set.EqOn f (fun _ => 0) (K.space \ interior N)) :
    ∃ (g : E → F) (k : NNReal), IsPiecewiseAffineOn g _root_.Set.univ ∧ LipschitzWith k g ∧
      _root_.Set.EqOn g f K.space ∧ _root_.Set.EqOn g (fun _ => 0) Nᶜ ∧
      ∀ x, g x ∈ convexHull ℝ (_root_.Insert.insert 0 (f '' K.space)) := by
  obtain ⟨r, hr⟩ := ((isPolyhedron_space K).isCompact.union hN.isCompact).isBounded.subset_ball (0 :
      E)
  obtain ⟨T, hT, hTcard, hTP⟩ := exists_affineIndependent_openSimplex_superset
    (Module.finrank ℝ E) rfl (_root_.Metric.isBounded_ball (x := (0 : E)) (r := r))
  let P := simplexComplex T hT
  have : Finite P.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hPspace : P.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hNP : N ⊆ interior P.space := by
    apply (subset_union_right.trans hr).trans
    apply interior_maximal _ _root_.Metric.isOpen_ball
    rw [hPspace]
    exact hTP.trans (openSimplex_subset_convexHull T)
  have hKP : K.space ⊆ P.space := by
    apply (subset_union_left.trans hr).trans
    rw [hPspace]
    exact hTP.trans (openSimplex_subset_convexHull T)
  let Q : K.faces ⊕ Unit → Set E := Sum.elim
    (fun s => convexHull ℝ ((s : Finset E) : Set E)) (fun _ => N)
  have hQ : ∀ i, IsPolyhedron (Q i) := by
    rintro (s | _)
    · exact isPolyhedron_convexHull_of_affineIndependent _ (K.indep s.property)
    · exact hN
  have hQP : ∀ i, Q i ⊆ P.space := by
    rintro (s | _)
    · exact (K.convexHull_subset_space s.property).trans hKP
    · exact hNP.trans interior_subset
  obtain ⟨R, hR, hRfinite, hcover⟩ := exists_isSubdivision_subcomplexes P Q hQ hQP
  have : Finite R.faces := hRfinite.to_subtype
  have hRN : (restrict R N).space = N := restrict_space_of_eq_biUnion R N (hcover (Sum.inr ()))
  let ψ : E → F := fun v => if v ∈ K.space then f v else 0
  let g := simplicialMap R ψ
  have hfix : _root_.Set.EqOn g f K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    have hscover := hcover (Sum.inl ⟨s, hs⟩)
    change convexHull ℝ (s : Set E) = _ at hscover
    rw [hscover] at hxs
    obtain ⟨t, ⟨ht, hts⟩, hxt⟩ := mem_iUnion₂.mp hxs
    obtain ⟨A, hA⟩ := hf s hs
    rw [show g x = ∑ v ∈ t, weights t x v • ψ v from simplicialMap_eq_of_mem R ψ ht hxt]
    calc ∑ v ∈ t, weights t x v • ψ v = ∑ v ∈ t, weights t x v • A v := by
          apply Finset.sum_congr rfl
          intro v hv
          have hvs := hts (subset_convexHull ℝ _ hv)
          rw [show ψ v = f v from if_pos (K.convexHull_subset_space hs hvs), hA hvs]
      _ = A (∑ v ∈ t, weights t x v • v) := (affineMap_apply_sum_smul A (sum_weights hxt)).symm
      _ = f x := by rw [sum_weights_smul hxt, ← hA (hts hxt)]
  have hzeroN : _root_.Set.EqOn g (fun _ => 0) Nᶜ := by
    intro x hxN
    by_cases hxR : x ∈ R.space
    · obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp hxR
      have hvs : ∀ v ∈ s, ψ v = 0 := by
        intro v hv
        by_cases hvK : v ∈ K.space
        · rw [show ψ v = f v from if_pos hvK]
          apply hzero
          refine ⟨hvK, fun hvN => ?_⟩
          have hvN' : v ∈ interior (restrict R N).space := by rwa [hRN]
          have hsub := convexHull_subset_of_mem_interior_subcomplex R (restrict R N)
            (restrict_faces_subset R N) hs (subset_convexHull ℝ _ hv) hvN'
          apply hxN
          rw [← hRN]
          exact hsub hxs
        · exact if_neg hvK
      rw [show g x = ∑ v ∈ s, weights s x v • ψ v from simplicialMap_eq_of_mem R ψ hs hxs]
      exact Finset.sum_eq_zero fun v hv => by rw [hvs v hv, smul_zero]
    · simp only [g, simplicialMap, carrierFace, dif_neg hxR, Finset.sum_empty]
  have hgP : IsPiecewiseAffineOn g (interior P.space) :=
    (isPiecewiseAffineOn_simplicialMap R ψ).mono isOpen_interior
      (by rw [hR.space_eq]; exact interior_subset)
  have hgN : IsPiecewiseAffineOn g Nᶜ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (0 : F))
        hN.isCompact.isClosed.isOpen_compl).congr hzeroN
  have hg : IsPiecewiseAffineOn g univ := by
    intro x _
    by_cases hxP : x ∈ interior P.space
    · have h : IsPiecewiseAffineWithinAt g (_root_.Set.univ ∩ interior P.space) x := by
        simpa only [_root_.Set.univ_inter] using hgP x hxP
      exact h.of_inter_of_mem_nhds (isOpen_interior.mem_nhds hxP)
    · have hxN : x ∈ Nᶜ := fun hx => hxP (hNP hx)
      have h : IsPiecewiseAffineWithinAt g (_root_.Set.univ ∩ Nᶜ) x := by
        simpa only [_root_.Set.univ_inter] using hgN x hxN
      exact h.of_inter_of_mem_nhds (hN.isCompact.isClosed.isOpen_compl.mem_nhds hxN)
  obtain ⟨k, hk⟩ := hg.exists_lipschitzWith_of_eq_zero_off hN.isCompact hzeroN
  refine ⟨g, k, hg, hk, hfix, hzeroN, fun x => ?_⟩
  have hmem : ∀ v, ψ v ∈ convexHull ℝ (_root_.Insert.insert 0 (f '' K.space)) := by
    intro v
    apply subset_convexHull ℝ _
    by_cases hv : v ∈ K.space
    · rw [show ψ v = f v from if_pos hv]
      exact Or.inr ⟨v, hv, rfl⟩
    · rw [show ψ v = 0 from if_neg hv]
      exact _root_.Set.mem_insert 0 _
  by_cases hxR : x ∈ R.space
  · obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp hxR
    rw [show g x = ∑ v ∈ s, weights s x v • ψ v from simplicialMap_eq_of_mem R ψ hs hxs]
    exact (convex_convexHull ℝ _).sum_mem (fun v hv => weights_nonneg hxs hv) (sum_weights hxs)
      (fun v _ => hmem v)
  · simp only [g, simplicialMap, carrierFace, dif_neg hxR, Finset.sum_empty]
    exact subset_convexHull ℝ _ (_root_.Set.mem_insert 0 _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_extension_of_eq_zero_on_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_extension_of_eq_zero_on_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_extension_of_eq_zero_on_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_extension_of_eq_zero_on_faces

theorem IsPiecewiseAffineOn.exists_lipschitz_extension_of_eq_zero [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {P N : Set E}
    (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P) (hN : IsPolyhedron N)
    (hzero : _root_.Set.EqOn f (fun _ => 0) (P \ interior N)) :
    ∃ (g : E → F) (k : NNReal), IsPiecewiseAffineOn g _root_.Set.univ ∧ LipschitzWith k g ∧
      EqOn g f P ∧ _root_.Set.EqOn g (fun _ => 0) Nᶜ ∧ ∀ x, g x ∈ convexHull ℝ (_root_.Insert.insert 0 (f '' P)) := by
  obtain ⟨K, hfinite, hspace⟩ := hP.exists_simplicialComplex
  have : Finite K.faces := hfinite.to_subtype
  have hfK : IsPiecewiseAffineOn f K.space := by rwa [hspace]
  obtain ⟨K', hK', hfinite', hfaces⟩ := hfK.exists_isSubdivision_affineOn_faces K
  have : Finite K'.faces := hfinite'.to_subtype
  have hspace' : K'.space = P := hK'.space_eq.trans hspace
  have hzero' : _root_.Set.EqOn f (fun _ => 0) (K'.space \ interior N) := by rwa [hspace']
  simpa only [hspace'] using
    exists_piecewiseAffine_lipschitz_extension_of_eq_zero_on_faces K' f hfaces hN hzero'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_lipschitz_extension_of_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_lipschitz_extension_of_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_lipschitz_extension_of_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_lipschitz_extension_of_eq_zero

theorem IsPiecewiseAffineOn.univ_of_eqOn_compl [FiniteDimensional ℝ E]
    {f : E → E} {P : Set E} (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P)
    (hcont : Continuous f) (hfix : _root_.Set.EqOn f id Pᶜ) : IsPiecewiseAffineOn f univ := by
  have hneg : IsPiecewiseAffineOn (fun x : E => -x) P :=
    (isPiecewiseAffineOn_of_affine (-AffineMap.id ℝ E) isOpen_univ).mono_of_isPolyhedron
      hP (_root_.Set.subset_univ _)
  have hsub : IsPiecewiseAffineOn (fun x => f x - x) P := by
    simpa only [sub_eq_add_neg] using hf.add hneg
  have hzero : _root_.Set.EqOn (fun x => f x - x) (fun _ => 0) (P \ interior P) := by
    intro x hx
    have hxcl : x ∈ closure Pᶜ := by rw [closure_compl]; exact hx.2
    change f x - x = 0
    rw [hfix.closure hcont continuous_id hxcl, id_eq, sub_self]
  obtain ⟨g, _, hg, _, hgf, hgzero, _⟩ :=
    hsub.exists_lipschitz_extension_of_eq_zero hP hP hzero
  apply ((isPiecewiseAffineOn_id isOpen_univ).add hg).congr
  intro x _
  change f x = x + g x
  by_cases hx : x ∈ P
  · rw [hgf hx]
    change f x = x + (f x - x)
    simp only [sub_eq_add_neg, add_left_comm x, add_neg_cancel, add_zero]
  · rw [hgzero hx, add_zero]
    exact hfix hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.univ_of_eqOn_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.univ_of_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.univ_of_eqOn_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.univ_of_eqOn_compl

theorem IsPLHomeomorphOn.univ_of_eqOn_compl [FiniteDimensional ℝ E]
    {h : E ≃ₜ E} {P : Set E} (hh : IsPLHomeomorphOn h P P)
    (hP : IsPolyhedron P) (hfix : _root_.Set.EqOn h id Pᶜ) : IsPLHomeomorphOn h _root_.Set.univ univ := by
  have hfix' : _root_.Set.EqOn h.symm id Pᶜ := by
    intro x hx
    exact h.symm_apply_eq.mpr (hfix hx).symm
  have hinv := hh.homeomorph_symm.isPiecewiseAffineOn.univ_of_eqOn_compl
    hP h.continuous_symm hfix'
  have hbij : _root_.Set.BijOn h _root_.Set.univ univ := h.bijective.bijOn_univ
  refine ⟨hbij, hh.isPiecewiseAffineOn.univ_of_eqOn_compl hP h.continuous hfix, ?_⟩
  exact hinv.congr fun x hx =>
    h.injective ((hbij.invOn_invFunOn.2 hx).trans (h.apply_symm_apply x).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.univ_of_eqOn_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.univ_of_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.univ_of_eqOn_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.univ_of_eqOn_compl

theorem IsPLHomeomorphOn.exists_extension_of_eqOn_frontier [FiniteDimensional ℝ E]
    {f : E → E} {P : Set E} (hf : IsPLHomeomorphOn f P P) (hP : IsPolyhedron P)
    (hfix : _root_.Set.EqOn f id (frontier P)) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn h f P ∧ _root_.Set.EqOn h id Pᶜ := by
  classical
  let f' := Function.invFunOn f P
  have hmaps' : _root_.Set.MapsTo f' P P := hf.bijOn.surjOn.mapsTo_invFunOn
  have hinv : _root_.Set.InvOn f' f P P := hf.bijOn.invOn_invFunOn
  have hfix' : _root_.Set.EqOn f' id (frontier P) := by
    intro x hx
    have hxP := hP.isCompact.isClosed.frontier_subset hx
    have hfx : f x = x := hfix hx
    exact (congrArg f' hfx).symm.trans (hinv.1 hxP)
  let g := P.piecewise f id
  let g' := P.piecewise f' id
  have hgf : Function.LeftInverse g' g := by
    intro x
    by_cases hx : x ∈ P
    · simp only [g, g', _root_.Set.piecewise_eq_of_mem P f id hx,
        _root_.Set.piecewise_eq_of_mem P f' id (hf.bijOn.mapsTo hx), hinv.1 hx]
    · simp only [g, g', _root_.Set.piecewise_eq_of_notMem P f id hx, id_eq,
        _root_.Set.piecewise_eq_of_notMem P f' id hx]
  have hfg : Function.RightInverse g' g := by
    intro x
    by_cases hx : x ∈ P
    · simp only [g, g', _root_.Set.piecewise_eq_of_mem P f' id hx,
        _root_.Set.piecewise_eq_of_mem P f id (hmaps' hx), hinv.2 hx]
    · simp only [g, g', _root_.Set.piecewise_eq_of_notMem P f' id hx, id_eq,
        _root_.Set.piecewise_eq_of_notMem P f id hx]
  have hcontinuous {k : E → E} (hk : ContinuousOn k P) (hboundary : _root_.Set.EqOn k id (frontier P)) :
      Continuous (P.piecewise k id) :=
    continuous_piecewise hboundary (by simpa only [hP.isCompact.isClosed.closure_eq] using hk)
      continuous_id.continuousOn
  let h : E ≃ₜ E :=
    { toEquiv := Equiv.mk g g' hgf hfg
      continuous_toFun := hcontinuous hf.isPiecewiseAffineOn.continuousOn hfix
      continuous_invFun := hcontinuous hf.isPiecewiseAffineOn_invFunOn.continuousOn hfix' }
  have hPfix : _root_.Set.EqOn h f P := fun x hx => by change g x = f x; exact _root_.Set.piecewise_eq_of_mem P f id hx
  have hcomplement : _root_.Set.EqOn h id Pᶜ := fun x hx => by
    change g x = x
    exact _root_.Set.piecewise_eq_of_notMem P f id hx
  exact ⟨h, (hf.congr hPfix).univ_of_eqOn_compl hP hcomplement, hPfix, hcomplement⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_of_eqOn_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_of_eqOn_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_of_eqOn_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_of_eqOn_frontier

theorem IsPLHomeomorphOn.exists_extension_on_polyhedron [FiniteDimensional ℝ E]
    {f : E → E} {C M U : Set E} (hf : IsPLHomeomorphOn f C C)
    (hC : IsPolyhedron C) (hM : IsPolyhedron M) (hCM : C ⊆ M)
    (hU : IsOpen U) (hUC : U ∩ M ⊆ C) (hfix : _root_.Set.EqOn f id (frontier C \ U)) :
    ∃ G : E → E, IsPLHomeomorphOn G M M ∧ _root_.Set.EqOn G f C ∧
      EqOn G id (closure (M \ C)) := by
  classical
  let Q := closure (M \ C)
  have hQ : IsPolyhedron Q := hM.closure_sdiff hC
  have hQM : Q ⊆ M := closure_minimal _root_.Set.sdiff_subset hM.isClosed
  have hQU : Q ⊆ Uᶜ := by
    apply closure_minimal ?_ hU.isClosed_compl
    rintro x ⟨hxM, hxC⟩ hxU
    exact hxC (hUC ⟨hxU, hxM⟩)
  have hfront : C ∩ Q ⊆ frontier C := by
    rintro x ⟨hxC, hxQ⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxC, closure_mono (fun _ hx => hx.2) hxQ⟩
  have hfixQ : _root_.Set.EqOn f id (C ∩ Q) := fun _ hx => hfix ⟨hfront hx, hQU hx.2⟩
  have hQId : IsPLHomeomorphOn (id : E → E) Q Q :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hQ
      ((isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron hQ (_root_.Set.subset_univ Q))
      (_root_.Set.bijOn_id Q)
  have hcover : C ∪ Q = M := by
    apply Subset.antisymm (_root_.Set.union_subset hCM hQM)
    intro x hx
    by_cases hxC : x ∈ C
    · exact Or.inl hxC
    · exact Or.inr (subset_closure ⟨hx, hxC⟩)
  have hG := hf.piecewise hQId hC hQ hfixQ (hfixQ.image_eq.trans (_root_.Set.image_id _))
  rw [hcover] at hG
  refine ⟨C.piecewise f id, hG, C.piecewise_eqOn f id, ?_⟩
  intro x hx
  by_cases hxC : x ∈ C
  · rw [C.piecewise_eq_of_mem f id hxC]
    exact hfixQ ⟨hxC, hx⟩
  · exact C.piecewise_eq_of_notMem f id hxC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_on_polyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_on_polyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_on_polyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_extension_on_polyhedron

open _root_.Classical in
theorem exists_piecewiseAffine_lipschitz_vertex_function_of_openStar [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E)
    {N : Set E} (hN : IsPolyhedron N) (hstar : openStar K p ⊆ interior N) :
    ∃ (b : E → ℝ) (k : NNReal), IsPiecewiseAffineOn b _root_.Set.univ ∧ LipschitzWith k b ∧
      _root_.Set.EqOn b (simplicialMap K (fun w => if w = p then 1 else 0)) K.space ∧
      EqOn b (fun _ => 0) Nᶜ := by
  classical
  let f := simplicialMap K (fun w => if w = p then (1 : ℝ) else 0)
  have hzero : _root_.Set.EqOn f (fun _ => 0) (K.space \ interior N) := by
    intro x hx
    have hxavoid : x ∈ avoidingUnion K p := by
      by_contra hxavoid
      exact hx.2 (hstar ⟨hx.1, hxavoid⟩)
    obtain ⟨s, ⟨hs, hps⟩, hxs⟩ := mem_iUnion₂.mp hxavoid
    rw [show f x = ∑ w ∈ s, weights s x w • (if w = p then (1 : ℝ) else 0) from
      simplicialMap_eq_of_mem K _ hs hxs]
    exact Finset.sum_eq_zero fun w hw => by
      rw [if_neg (ne_of_mem_of_not_mem hw hps), smul_zero]
  obtain ⟨b, k, hb, hk, hfix, hzero, -⟩ :=
    (isPiecewiseAffineOn_simplicialMap K _).exists_lipschitz_extension_of_eq_zero
      (isPolyhedron_space K) hN hzero
  exact ⟨b, k, hb, hk, hfix, hzero⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_vertex_function_of_openStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_vertex_function_of_openStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_vertex_function_of_openStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffine_lipschitz_vertex_function_of_openStar

open _root_.Classical in
theorem exists_isPLHomeomorphOn_of_small_vertex_move [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E)
    {N : Set E} (hN : IsPolyhedron N) (hstar : openStar K p ⊆ interior N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : E, _root_.Dist.dist q p < δ →
      ∃ h : E ≃ₜ E, IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn h id Nᶜ ∧
        EqOn h (simplicialMap K (Function.update id p q)) K.space := by
  classical
  obtain ⟨b, k, hb, hk, hfix, hzero⟩ :=
    exists_piecewiseAffine_lipschitz_vertex_function_of_openStar K p hN hstar
  let δ : ℝ := 1 / ((k : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, fun q hq => ?_⟩
  let d : E → E := fun x => b x • (q - p)
  have hd : IsPiecewiseAffineOn d univ :=
    (hb.affine_comp (LinearMap.toSpanSingleton ℝ E (q - p)).toAffineMap).congr (fun _ _ => rfl)
  have hdlip : LipschitzWith (k * ‖q - p‖₊) d := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change _root_.Dist.dist (b x • (q - p)) (b y • (q - p)) ≤ _
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, ← Real.dist_eq]
    calc _root_.Dist.dist (b x) (b y) * ‖q - p‖ ≤ ((k : ℝ) * _root_.Dist.dist x y) * ‖q - p‖ :=
          mul_le_mul_of_nonneg_right (hk.dist_le_mul x y) (norm_nonneg _)
      _ = (k * ‖q - p‖₊ : NNReal) * _root_.Dist.dist x y := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
  have hsmall : k * ‖q - p‖₊ < 1 := by
    change (k : ℝ) * ‖q - p‖ < 1
    have hq' : ‖q - p‖ < δ := by simpa only [dist_eq_norm] using hq
    have hδeq : δ * ((k : ℝ) + 1) = 1 := div_mul_cancel₀ 1 (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hq'.le k.property
    calc (k : ℝ) * ‖q - p‖ ≤ (k : ℝ) * δ := hmul
      _ = 1 - δ := by
        calc (k : ℝ) * δ = δ * ((k : ℝ) + 1) - δ := by ring
          _ = 1 - δ := by rw [hδeq]
      _ < 1 := sub_lt_self _ hδ
  have hh := isPLHomeomorphOn_id_add_of_lipschitz hd hdlip hsmall
  let e := (Homeomorph.Set.univ E).symm.trans (hh.homeomorph.trans (Homeomorph.Set.univ E))
  refine ⟨e, hh, ?_, ?_⟩
  · intro x hx
    change x + b x • (q - p) = x
    rw [hzero hx, zero_smul, add_zero]
  · intro x hx
    change x + b x • (q - p) = simplicialMap K (Function.update id p q) x
    rw [hfix hx]
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    rw [simplicialMap_eq_of_mem K _ hs hxs, simplicialMap_eq_of_mem K _ hs hxs]
    rw [Finset.sum_smul]
    conv_lhs => arg 1; rw [← sum_weights_smul hxs]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hwp : w = p
    · subst w
      simp only [if_true, smul_eq_mul, mul_one, Function.update_self, smul_sub]
      abel
    · simp only [hwp, if_false, smul_eq_mul, _root_.MulZeroClass.mul_zero, zero_smul, add_zero,
        Function.update_of_ne hwp, id_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_small_vertex_move then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_small_vertex_move"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_small_vertex_move ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_of_small_vertex_move

end DifferentialGeometry.Topology.PiecewiseLinear
