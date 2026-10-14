import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem mfderiv_parameter_slice {A : ℝ × M → N} {t : ℝ} {x : M}
    (hA : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) A (t, x))
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y => A (t, y)) x v =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) A (t, x) (0, v) := by
  have h := mfderiv_comp x hA
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id :
      MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (fun y : M => (t, y)) x)
  rw [mfderiv_prod_right] at h
  exact congrArg (fun L => L v) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_parameter_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_parameter_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_parameter_slice ``Submission.DifferentialGeometry.Geometry.mfderiv_parameter_slice

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem mfderiv_parameter_time {A : ℝ × M → N} {t : ℝ} {x : M}
    (hA : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) A (t, x))
    (v : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun r => A (r, x)) t v =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) A (t, x) (v, 0) := by
  have h := mfderiv_comp t hA
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const :
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (fun r : ℝ => (r, x)) t)
  dsimp only [id] at h
  rw [mfderiv_prod_left] at h
  exact congrArg (fun L => L v) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_parameter_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_parameter_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_parameter_time ``Submission.DifferentialGeometry.Geometry.mfderiv_parameter_time

set_option backward.isDefEq.respectTransparency false in


theorem contMDiffOn_parameter_tangentMap {A : ℝ × M → N} {T : Set ℝ}
    (hT : IsOpen T)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ A (T ×ˢ _root_.Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => TotalSpace.mk' F (A (q.1, q.2.proj))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y => A (q.1, y)) q.2.proj q.2.2)) (T ×ˢ _root_.Set.univ) := by
  let J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)
  let lift : ℝ × TangentBundle 𝓘(ℝ, E) M → TangentBundle J (ℝ × M) := fun q =>
    TotalSpace.mk' (ℝ × E) (q.1, q.2.proj) (0, q.2.2)
  have hzero : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M =>
        TotalSpace.mk' ℝ (E := TangentSpace 𝓘(ℝ, ℝ)) q.1 0) :=
    (_root_.Bundle.contMDiff_zeroSection (F := ℝ) (IB := 𝓘(ℝ, ℝ)) ℝ (TangentSpace 𝓘(ℝ, ℝ))).comp contMDiff_fst
  have hlift : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E)))
      (J.prod 𝓘(ℝ, ℝ × E)) ∞ lift :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))).comp
      (hzero.prodMk contMDiff_snd)
  have hopen : IsOpen (T ×ˢ (_root_.Set.univ : Set M)) := hT.prod isOpen_univ
  have htan := hA.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hopen.uniqueMDiffOn
  apply (htan.comp hlift.contMDiffOn (fun q hq => ⟨hq.1, _root_.Set.mem_univ _⟩)).congr
  intro q hq
  dsimp only [Function.comp_apply, tangentMapWithin, lift]
  rw [mfderivWithin_of_mem_nhds (hopen.mem_nhds ⟨hq.1, _root_.Set.mem_univ _⟩)]
  congr 1
  exact mfderiv_parameter_slice
    (((hA _ ⟨hq.1, _root_.Set.mem_univ _⟩).contMDiffAt (hopen.mem_nhds ⟨hq.1, _root_.Set.mem_univ _⟩)).mdifferentiableAt (by simp)) q.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap ``Submission.DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap

end DifferentialGeometry.Geometry

end

section

noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem mfderivWithin_parameter_slice {A : ℝ × M → N} {T : Set ℝ} {t : ℝ} {x : M}
    (ht : t ∈ T)
    (hA : MDifferentiableWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) A
      (T ×ˢ _root_.Set.univ) (t, x)) (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y => A (t, y)) x v =
      mfderivWithin (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) A
        (T ×ˢ _root_.Set.univ) (t, x) (0, v) := by
  have h := mfderivWithin_comp x hA
    ((mdifferentiableAt_const.prodMk mdifferentiableAt_id :
      MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
        (fun y : M => (t, y)) x).mdifferentiableWithinAt (s := _root_.Set.univ))
    (show _root_.Set.MapsTo (fun y : M => (t, y)) _root_.Set.univ (T ×ˢ _root_.Set.univ) from fun _ _ => ⟨ht, trivial⟩)
    (uniqueMDiffWithinAt_univ 𝓘(ℝ, E))
  simp only [mfderivWithin_univ, mfderiv_prod_right] at h
  exact congrArg (fun L => L v) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderivWithin_parameter_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderivWithin_parameter_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderivWithin_parameter_slice ``Submission.DifferentialGeometry.Geometry.mfderivWithin_parameter_slice

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_parameter_tangentMap_of_uniqueDiffOn {A : ℝ × M → N} {T : Set ℝ}
    (hT : UniqueDiffOn ℝ T)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ A (T ×ˢ _root_.Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => TotalSpace.mk' F (A (q.1, q.2.proj))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y => A (q.1, y)) q.2.proj q.2.2)) (T ×ˢ _root_.Set.univ) := by
  let J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)
  let lift : ℝ × TangentBundle 𝓘(ℝ, E) M → TangentBundle J (ℝ × M) := fun q =>
    TotalSpace.mk' (ℝ × E) (q.1, q.2.proj) (0, q.2.2)
  have hzero : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M =>
        TotalSpace.mk' ℝ (E := TangentSpace 𝓘(ℝ, ℝ)) q.1 0) :=
    (_root_.Bundle.contMDiff_zeroSection (F := ℝ) (IB := 𝓘(ℝ, ℝ)) ℝ (TangentSpace 𝓘(ℝ, ℝ))).comp contMDiff_fst
  have hlift : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E)))
      (J.prod 𝓘(ℝ, ℝ × E)) ∞ lift :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))).comp
      (hzero.prodMk contMDiff_snd)
  have hprod : UniqueMDiffOn J (T ×ˢ (_root_.Set.univ : Set M)) :=
    hT.uniqueMDiffOn.prod uniqueMDiffOn_univ
  have htan := hA.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hprod
  apply (htan.comp hlift.contMDiffOn (fun q hq => ⟨hq.1, _root_.Set.mem_univ _⟩)).congr
  intro q hq
  dsimp only [Function.comp_apply, tangentMapWithin, lift]
  congr 1
  exact mfderivWithin_parameter_slice hq.1
    ((hA _ ⟨hq.1, _root_.Set.mem_univ _⟩).mdifferentiableWithinAt (by simp)) q.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap_of_uniqueDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap_of_uniqueDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap_of_uniqueDiffOn ``Submission.DifferentialGeometry.Geometry.contMDiffOn_parameter_tangentMap_of_uniqueDiffOn

end DifferentialGeometry.Geometry

end

end
