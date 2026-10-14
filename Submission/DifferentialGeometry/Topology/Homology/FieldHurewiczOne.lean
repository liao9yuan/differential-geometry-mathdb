/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.FieldCycles
import Submission.DifferentialGeometry.Topology.Homology.PathHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

variable {k X : Type} [Field k] [TopologicalSpace X]

noncomputable def fieldVertexChain (x : X) : (fieldSingularChains (k := k) (X := X)).X 0 :=
  fieldSimplexChain (k := k) 0 (TopCat.toSSetObj₀Equiv.symm x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldVertexChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldVertexChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldVertexChain ``Submission.DifferentialGeometry.Topology.fieldVertexChain

theorem fieldPathChain_boundary {x y : X} (p : Path x y) :
    (fieldSingularChains (k := k) (X := X)).d 1 0 (fieldPathChain (k := k) p) =
      fieldVertexChain (k := k) y - fieldVertexChain (k := k) x := by
  change (fieldSingularChains (k := k) (X := X)).d 1 0
    (fieldSimplexChain (k := k) 1 (TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv.symm p).hom)) = _
  rw [fieldSimplexChain_boundary_one]
  simp only [TopCat.δ_zero_toSSetObj₁Equiv.symm, TopCat.δ_one_toSSetObj₁Equiv.symm]
  change fieldVertexChain (k := k) (p 1) - fieldVertexChain (k := k) (p 0) = _
  rw [Path.target, Path.source]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldPathChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldPathChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldPathChain_boundary ``Submission.DifferentialGeometry.Topology.fieldPathChain_boundary

theorem pathConcatenationSimplex_field_boundary {a b c : X} (p : Path a b) (q : Path b c) :
    (fieldSingularChains (k := k) (X := X)).d 2 1
      (fieldSimplexChain (k := k) 2 (pathConcatenationSimplex p q)) =
        fieldPathChain (k := k) q - fieldPathChain (k := k) (p.trans q) +
          fieldPathChain (k := k) p := by
  rw [fieldSimplexChain_boundary_two, pathConcatenationSimplex_faces p q 0,
    pathConcatenationSimplex_faces p q 1, pathConcatenationSimplex_faces p q 2]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatenationSimplex_field_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatenationSimplex_field_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatenationSimplex_field_boundary ``Submission.DifferentialGeometry.Topology.pathConcatenationSimplex_field_boundary

theorem fieldPathChain_sub_mem_range_of_homotopic {a b : X} {p q : Path a b}
    (h : Path.Homotopic p q) :
    fieldPathChain (k := k) p - fieldPathChain (k := k) q ∈
      LinearMap.range ((fieldSingularChains (k := k) (X := X)).d 2 1).hom := by
  obtain ⟨F⟩ := h
  refine ⟨fieldSimplexChain (k := k) 2 (pathHomotopyLowerSimplex F) -
    fieldSimplexChain (k := k) 2 (pathHomotopyUpperSimplex F) -
    fieldSimplexChain (k := k) 2 (pathConcatenationSimplex (Path.refl b) (Path.refl b)) +
    fieldSimplexChain (k := k) 2 (pathConcatenationSimplex (Path.refl a) (Path.refl a)), ?_⟩
  simp only [map_add, map_sub, fieldSimplexChain_boundary_two,
    pathHomotopyLowerSimplex_faces, pathHomotopyUpperSimplex_faces,
    pathConcatenationSimplex_faces, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Path.refl_trans_refl]
  change fieldPathChain (k := k) (Path.refl b) -
      fieldPathChain (k := k) (pathHomotopyDiagonal F) + fieldPathChain (k := k) p -
      (fieldPathChain (k := k) q - fieldPathChain (k := k) (pathHomotopyDiagonal F) +
        fieldPathChain (k := k) (Path.refl a)) -
      (fieldPathChain (k := k) (Path.refl b) - fieldPathChain (k := k) (Path.refl b) +
        fieldPathChain (k := k) (Path.refl b)) +
      (fieldPathChain (k := k) (Path.refl a) - fieldPathChain (k := k) (Path.refl a) +
        fieldPathChain (k := k) (Path.refl a)) = _
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldPathChain_sub_mem_range_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldPathChain_sub_mem_range_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldPathChain_sub_mem_range_of_homotopic ``Submission.DifferentialGeometry.Topology.fieldPathChain_sub_mem_range_of_homotopic

noncomputable def fieldLoopCycle {x : X} (p : Path x x) :
    fieldSingularCycles (k := k) (X := X) 0 :=
  ⟨fieldPathChain (k := k) p, by rw [LinearMap.mem_ker, fieldPathChain_boundary, sub_self]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldLoopCycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldLoopCycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldLoopCycle ``Submission.DifferentialGeometry.Topology.fieldLoopCycle

noncomputable def fieldLoopHomologyClass {x : X} (p : Path x x) :
    (fieldSingularChains (k := k) (X := X)).homology 1 :=
  (fieldSingularHomologyCycleEquiv (k := k) (X := X) 0).symm
    (Submodule.Quotient.mk (fieldLoopCycle (k := k) p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldLoopHomologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldLoopHomologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldLoopHomologyClass ``Submission.DifferentialGeometry.Topology.fieldLoopHomologyClass

theorem fieldLoopHomologyClass_eq_of_sub_mem_range {x : X} {p q : Path x x}
    (h : fieldPathChain (k := k) p - fieldPathChain (k := k) q ∈
      LinearMap.range ((fieldSingularChains (k := k) (X := X)).d 2 1).hom) :
    fieldLoopHomologyClass (k := k) p = fieldLoopHomologyClass (k := k) q := by
  apply (fieldSingularHomologyCycleEquiv (k := k) (X := X) 0).injective
  simp only [fieldLoopHomologyClass, LinearEquiv.apply_symm_apply]
  apply (Submodule.Quotient.eq _).mpr
  obtain ⟨c, hc⟩ := h
  exact ⟨c, Subtype.ext hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_sub_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_sub_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_sub_mem_range ``Submission.DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_sub_mem_range

theorem fieldLoopHomologyClass_eq_of_homotopic {x : X} {p q : Path x x}
    (h : Path.Homotopic p q) :
    fieldLoopHomologyClass (k := k) p = fieldLoopHomologyClass (k := k) q :=
  fieldLoopHomologyClass_eq_of_sub_mem_range (fieldPathChain_sub_mem_range_of_homotopic h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.fieldLoopHomologyClass_eq_of_homotopic

theorem fieldLoopHomologyClass_refl (x : X) :
    fieldLoopHomologyClass (k := k) (Path.refl x) = 0 := by
  apply (fieldSingularHomologyCycleEquiv (k := k) (X := X) 0).injective
  rw [map_zero]
  simp only [fieldLoopHomologyClass, LinearEquiv.apply_symm_apply]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨fieldSimplexChain (k := k) 2
    (pathConcatenationSimplex (Path.refl x) (Path.refl x)), ?_⟩
  apply Subtype.ext
  change (fieldSingularChains (k := k) (X := X)).d 2 1 _ =
    fieldPathChain (k := k) (Path.refl x)
  rw [pathConcatenationSimplex_field_boundary, Path.refl_trans_refl, sub_self, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldLoopHomologyClass_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldLoopHomologyClass_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldLoopHomologyClass_refl ``Submission.DifferentialGeometry.Topology.fieldLoopHomologyClass_refl

theorem fieldLoopHomologyClass_trans {x : X} (p q : Path x x) :
    fieldLoopHomologyClass (k := k) (p.trans q) = fieldLoopHomologyClass (k := k) p +
      fieldLoopHomologyClass (k := k) q := by
  apply (fieldSingularHomologyCycleEquiv (k := k) (X := X) 0).injective
  rw [map_add]
  simp only [fieldLoopHomologyClass, LinearEquiv.apply_symm_apply]
  rw [← Submodule.Quotient.mk_add]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-fieldSimplexChain (k := k) 2 (pathConcatenationSimplex p q), ?_⟩
  apply Subtype.ext
  change (fieldSingularChains (k := k) (X := X)).d 2 1 _ =
    fieldPathChain (k := k) (p.trans q) -
      (fieldPathChain (k := k) p + fieldPathChain (k := k) q)
  rw [map_neg, pathConcatenationSimplex_field_boundary]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldLoopHomologyClass_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldLoopHomologyClass_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldLoopHomologyClass_trans ``Submission.DifferentialGeometry.Topology.fieldLoopHomologyClass_trans

noncomputable def fieldHurewiczOne (x : X) : FundamentalGroup X x →*
    Multiplicative ((fieldSingularChains (k := k) (X := X)).homology 1) where
  toFun := Quotient.lift (fun p => Multiplicative.ofAdd (fieldLoopHomologyClass (k := k) p))
    (fun _ _ h => congrArg Multiplicative.ofAdd (fieldLoopHomologyClass_eq_of_homotopic h))
  map_one' := congrArg Multiplicative.ofAdd (fieldLoopHomologyClass_refl x)
  map_mul' p q := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction q using Path.Homotopic.Quotient.ind with
      | mk q =>
        change Multiplicative.ofAdd (fieldLoopHomologyClass (k := k) (q.trans p)) =
          Multiplicative.ofAdd (fieldLoopHomologyClass (k := k) p +
            fieldLoopHomologyClass (k := k) q)
        rw [fieldLoopHomologyClass_trans, add_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldHurewiczOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldHurewiczOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldHurewiczOne ``Submission.DifferentialGeometry.Topology.fieldHurewiczOne

theorem fieldHurewiczOne_apply {x : X} (p : Path x x) :
    (fieldHurewiczOne (k := k) x (Path.Homotopic.Quotient.mk p)).toAdd =
      fieldLoopHomologyClass (k := k) p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldHurewiczOne_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldHurewiczOne_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldHurewiczOne_apply ``Submission.DifferentialGeometry.Topology.fieldHurewiczOne_apply

private noncomputable def fieldOneChainClass :
    (fieldSingularChains (k := k) (X := X)).X 1 →ₗ[k]
      (fieldSingularChains (k := k) (X := X)).X 1 ⧸
        LinearMap.range ((fieldSingularChains (k := k) (X := X)).d 2 1).hom :=
  (LinearMap.range ((fieldSingularChains (k := k) (X := X)).d 2 1).hom).mkQ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fieldOneChainClass
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fieldOneChainClass target :: scope.openDecls } }

private theorem fieldOneChainClass_path_trans {a b c : X} (p : Path a b) (q : Path b c) :
    fieldOneChainClass (fieldPathChain (k := k) (p.trans q)) =
      fieldOneChainClass (fieldPathChain (k := k) p) +
        fieldOneChainClass (fieldPathChain (k := k) q) := by
  rw [← map_add]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-fieldSimplexChain (k := k) 2 (pathConcatenationSimplex p q), ?_⟩
  rw [map_neg, pathConcatenationSimplex_field_boundary]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fieldOneChainClass_path_trans
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fieldOneChainClass_path_trans target :: scope.openDecls } }

private theorem fieldOneChainClass_path_refl (x : X) :
    fieldOneChainClass (fieldPathChain (k := k) (Path.refl x)) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨fieldSimplexChain (k := k) 2
    (pathConcatenationSimplex (Path.refl x) (Path.refl x)), ?_⟩
  rw [pathConcatenationSimplex_field_boundary, Path.refl_trans_refl, sub_self, zero_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fieldOneChainClass_path_refl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fieldOneChainClass_path_refl target :: scope.openDecls } }

private theorem fieldOneChainClass_path_symm {a b : X} (p : Path a b) :
    fieldOneChainClass (fieldPathChain (k := k) p.symm) =
      -fieldOneChainClass (fieldPathChain (k := k) p) := by
  have h : fieldOneChainClass (fieldPathChain (k := k) (p.trans p.symm)) =
      fieldOneChainClass (fieldPathChain (k := k) (Path.refl a)) :=
    (Submodule.Quotient.eq _).mpr
      (fieldPathChain_sub_mem_range_of_homotopic (Path.Homotopic.trans_symm p))
  rw [fieldOneChainClass_path_trans, fieldOneChainClass_path_refl] at h
  exact eq_neg_of_add_eq_zero_right h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fieldOneChainClass_path_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fieldOneChainClass_path_symm target :: scope.openDecls } }

theorem fieldHurewiczOne_span_range [PathConnectedSpace X] (x : X) :
    Submodule.span k (Set.range (fun a => (fieldHurewiczOne (k := k) x a).toAdd)) = ⊤ := by
  classical
  let C := fieldSingularChains (k := k) (X := X)
  let r := PathConnectedSpace.somePath x
  let loops (σ : integralSingularSimplex 1 X) : Path x x :=
    (r _).trans ((integralSimplexPath σ).trans (r _).symm)
  let g : C.X 1 →ₗ[k] fieldSingularCycles (k := k) (X := X) 0 :=
    (fieldSingularChainBasis (k := k) (X := X) 1).constr ℕ
      (fun σ => fieldLoopCycle (k := k) (loops σ))
  let v : C.X 0 →ₗ[k] C.X 1 :=
    (fieldSingularChainBasis (k := k) (X := X) 0).constr ℕ
      (fun σ => fieldPathChain (k := k) (r (TopCat.toSSetObj₀Equiv σ)))
  have hg (σ : integralSingularSimplex 1 X) :
      g (fieldSimplexChain (k := k) 1 σ) = fieldLoopCycle (k := k) (loops σ) := by
    rw [← fieldSingularChainBasis_apply]
    exact (fieldSingularChainBasis (k := k) (X := X) 1).constr_basis ℕ _ σ
  have hv (σ : integralSingularSimplex 0 X) :
      v (fieldSimplexChain (k := k) 0 σ) =
        fieldPathChain (k := k) (r (TopCat.toSSetObj₀Equiv σ)) := by
    rw [← fieldSingularChainBasis_apply]
    exact (fieldSingularChainBasis (k := k) (X := X) 0).constr_basis ℕ _ σ
  let q := fieldOneChainClass (k := k) (X := X)
  have hlinear : q.comp ((fieldSingularCycles (k := k) (X := X) 0).subtype.comp g) =
      q - q.comp (v.comp (C.d 1 0).hom) := by
    apply (fieldSingularChainBasis (k := k) (X := X) 1).ext
    intro σ
    rw [fieldSingularChainBasis_apply]
    change q (g (fieldSimplexChain (k := k) 1 σ)).val =
      q (fieldSimplexChain (k := k) 1 σ) -
        q (v (C.d 1 0 (fieldSimplexChain (k := k) 1 σ)))
    rw [hg, fieldSimplexChain_boundary_one, map_sub, hv, hv, map_sub]
    change fieldOneChainClass (fieldPathChain (k := k) ((r _).trans
      ((integralSimplexPath σ).trans (r _).symm))) = _
    rw [fieldOneChainClass_path_trans, fieldOneChainClass_path_trans,
      fieldOneChainClass_path_symm, fieldPathChain_simplexPath]
    abel
  let e := fieldSingularHomologyCycleEquiv (k := k) (X := X) 0
  let h := e.symm.toLinearMap.comp
    (LinearMap.range (fieldSingularBoundaryToCycles (k := k) (X := X) 0)).mkQ
  have hclass (c : fieldSingularCycles (k := k) (X := X) 0) : h (g c.val) = h c := by
    apply e.injective
    change e (e.symm _) = e (e.symm _)
    simp only [LinearEquiv.apply_symm_apply]
    apply (Submodule.Quotient.eq _).mpr
    have hc : C.d 1 0 c.val = 0 := c.property
    have heq := LinearMap.congr_fun hlinear c.val
    change q (g c.val).val = q c.val - q (v (C.d 1 0 c.val)) at heq
    rw [hc, map_zero, map_zero, sub_zero] at heq
    obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp heq
    exact ⟨b, Subtype.ext hb⟩
  let S := Submodule.span k (Set.range (fun a => (fieldHurewiczOne (k := k) x a).toAdd))
  have hmem (c : C.X 1) : h (g c) ∈ S := by
    have hc : c ∈ Submodule.span k
        (Set.range (fieldSingularChainBasis (k := k) (X := X) 1)) := by
      rw [(fieldSingularChainBasis (k := k) (X := X) 1).span_eq]
      exact Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨σ, rfl⟩ := hc
      rw [fieldSingularChainBasis_apply, hg]
      exact Submodule.subset_span ⟨Path.Homotopic.Quotient.mk (loops σ), rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add c d _ _ hc hd => simpa only [map_add] using S.add_mem hc hd
    | smul a c _ hc => simpa only [g.map_smul, h.map_smul] using S.smul_mem a hc
  apply Submodule.eq_top_iff'.mpr
  intro a
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e a)
  have hca : h c = a := by
    change e.symm (Submodule.Quotient.mk c) = a
    rw [hc, LinearEquiv.symm_apply_apply]
  rw [← hca, ← hclass c]
  exact hmem c.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldHurewiczOne_span_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldHurewiczOne_span_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldHurewiczOne_span_range ``Submission.DifferentialGeometry.Topology.fieldHurewiczOne_span_range

end DifferentialGeometry.Topology
