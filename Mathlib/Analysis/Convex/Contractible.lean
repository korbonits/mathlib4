/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# A convex set is contractible

In this file we prove that a (star) convex set in a real topological vector space is a contractible
topological space, and that a convex set in a real locally convex space is strongly locally
contractible.
-/

public section

open Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {s : Set E} {x : E}

/-- A non-empty star convex set is a contractible space. -/
protected theorem StarConvex.contractibleSpace (h : StarConvex ℝ x s) (hne : s.Nonempty) :
    ContractibleSpace s := by
  refine
    (contractible_iff_id_nullhomotopic s).2 ⟨⟨x, h.mem hne⟩,
      ⟨⟨⟨fun p ↦ ⟨p.1.1 • x + (1 - p.1.1) • (p.2 : E), ?_⟩, ?_⟩, fun x ↦ by simp, fun x ↦ by simp⟩⟩⟩
  · exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel _ _)
  · fun_prop

/-- A non-empty convex set is a contractible space. -/
protected theorem Convex.contractibleSpace (hs : Convex ℝ s) (hne : s.Nonempty) :
    ContractibleSpace s :=
  let ⟨_, hx⟩ := hne
  (hs.starConvex hx).contractibleSpace hne

instance (priority := 100) RealTopologicalVectorSpace.contractibleSpace : ContractibleSpace E :=
  (Homeomorph.Set.univ E).contractibleSpace_iff.mp <|
    convex_univ.contractibleSpace Set.univ_nonempty

/-- Convex subsets of real locally convex spaces are strongly locally contractible. -/
theorem Convex.stronglyLocallyContractibleSpace [LocallyConvexSpace ℝ E] (hs : Convex ℝ s) :
    StronglyLocallyContractibleSpace s := by
  refine .of_bases (fun x : s ↦ nhds_subtype s x ▸
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x.1).comap ((↑) : s → E)) fun x t ht ↦ ?_
  rw [← Subtype.preimage_coe_self_inter,
    (IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by simp)).contractibleSpace_iff]
  exact (hs.inter ht.2).contractibleSpace ⟨x, x.2, mem_of_mem_nhds ht.1⟩

/-- Real locally convex spaces are strongly locally contractible. -/
instance (priority := 100) LocallyConvexSpace.toStronglyLocallyContractibleSpace
    [LocallyConvexSpace ℝ E] : StronglyLocallyContractibleSpace E :=
  have := convex_univ (𝕜 := ℝ) (E := E) |>.stronglyLocallyContractibleSpace
  (Homeomorph.Set.univ E).symm.isOpenEmbedding.stronglyLocallyContractibleSpace
