/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Simple Polygons
-/

@[expose] public section

variable {R V P : Type*} [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]

variable (R) in
/-- A polygon is simple if non-adjacent edges are disjoint
and adjacent edges meet only at their shared vertex. -/
def Polygon.IsSimple (poly : Polygon P n) : Prop :=
  (∀ i j : Fin n, i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
    Disjoint (poly.edgeSet R i) (poly.edgeSet R j)) ∧
  (∀ i : Fin n,
    poly.edgeSet R i ∩ poly.edgeSet R (i + 1) = {poly (i + 1)})

namespace Polygon.IsSimple

variable {poly : Polygon P n}

theorem nonadjacent_disjoint {i j : Fin n} (h : poly.IsSimple R)
    (hij : i ≠ j) (hj : j ≠ i + 1) (hi : i ≠ j + 1) :
    Disjoint (poly.edgeSet R i) (poly.edgeSet R j) :=
  h.left i j hij hi hj

theorem adjacent_inter (i : Fin n) (h : poly.IsSimple R) :
    poly.edgeSet R i ∩ poly.edgeSet R (i + 1) = {poly (i + 1)} :=
  h.right i

end Polygon.IsSimple

/-! ### Boundary Map from AddCircle -/

namespace Polygon

open Set AffineMap

section BoundaryMap

variable {R V P : Type*} [Ring R] [LinearOrder R]
  [IsStrictOrderedRing R] [FloorRing R] [Archimedean R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]

/-- Piecewise-linear boundary parametrization on `R` by concatenating edges:
edge index = `⌊t⌋`, local parameter = `t - ⌊t⌋`. -/
noncomputable def boundaryParam (poly : Polygon P n) (t : R) : P :=
  let z : ℤ := Int.floor t
  let i : Fin n := ⟨z.toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  poly.edgePath (R := R) i (t - (z : R))

noncomputable def boundaryMap (poly : Polygon P n) : AddCircle (n : R) → P := by
  classical
  letI : Fact ((0 : R) < (n : R)) :=
    ⟨by
      have hn : 0 < n := Nat.pos_of_neZero n
      exact_mod_cast hn⟩
  exact AddCircle.liftIco (p := (n : R)) (a := (0 : R)) (poly.boundaryParam (R := R))

end BoundaryMap

namespace IsSimple

variable {R V P : Type*}
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable [Archimedean R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]

variable {poly : Polygon P n}

theorem boundaryMap_inj [IsDomain R] [Module.IsTorsionFree R V]
    (h : poly.IsSimple R) (nde : poly.HasNondegenerateEdges) :
    Function.Injective (poly.boundaryMap (R := R)) := by
  haveI : Fact ((0 : R) < (n : R)) := ⟨by
    have hn : 0 < n := Nat.pos_of_neZero n
    exact_mod_cast hn⟩
  intro x y heq
  obtain ⟨s, hs_mem, rfl⟩ := AddCircle.eq_coe_Ico x
  obtain ⟨t, ht_mem, rfl⟩ := AddCircle.eq_coe_Ico y
  have hs_mem' : s ∈ Ico (0 : R) n := by simpa [zero_add] using hs_mem
  have ht_mem' : t ∈ Ico (0 : R) n := by simpa [zero_add] using ht_mem
  simp only [boundaryMap] at heq
  rw [AddCircle.liftIco_coe_apply (by simpa [zero_add] using hs_mem),
      AddCircle.liftIco_coe_apply (by simpa [zero_add] using ht_mem)] at heq
  unfold boundaryParam at heq
  simp only [Int.self_sub_floor] at heq
  let sindex : Fin n := ⟨(Int.floor s).toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  let tindex : Fin n := ⟨(Int.floor t).toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  by_cases hindex : sindex = tindex
  · simp only [sindex, tindex] at hindex
    have hfrac : Int.fract s = Int.fract t := by
      rw [hindex] at heq
      exact lineMap_injective R (nde tindex) heq
    simp only [Fin.mk.injEq] at hindex
    have hfloor : ⌊s⌋ = ⌊t⌋ := by
      have hs_floor_nonneg : 0 ≤ ⌊s⌋ := Int.floor_nonneg.mpr hs_mem'.1
      have ht_floor_nonneg : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht_mem'.1
      have hs_floor_lt : ⌊s⌋ < n := by
        have h : (⌊s⌋ : R) < n := (Int.floor_le s).trans_lt hs_mem'.2
        exact_mod_cast h
      have ht_floor_lt : ⌊t⌋ < n := by
        have h : (⌊t⌋ : R) < n := (Int.floor_le t).trans_lt ht_mem'.2
        exact_mod_cast h
      have hs_toNat : (⌊s⌋).toNat = ⌊s⌋ := Int.toNat_of_nonneg hs_floor_nonneg
      have ht_toNat : (⌊t⌋).toNat = ⌊t⌋ := Int.toNat_of_nonneg ht_floor_nonneg
      have hs_mod : (⌊s⌋).toNat % n = (⌊s⌋).toNat := Nat.mod_eq_of_lt (by omega)
      have ht_mod : (⌊t⌋).toNat % n = (⌊t⌋).toNat := Nat.mod_eq_of_lt (by omega)
      omega
    have hst : s = t := by rw [← Int.floor_add_fract s, ← Int.floor_add_fract t, hfloor, hfrac]
    simp only [hst]
  · have hs_frac_mem : Int.fract s ∈ Ico (0 : R) 1 :=
      ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩
    have ht_frac_mem : Int.fract t ∈ Ico (0 : R) 1 :=
      ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩
    have hs_in_edge : poly.edgePath R sindex (Int.fract s) ∈ poly.edgeSet R sindex := by
      rw [edgeSet_eq_image_edgePath]
      exact ⟨Int.fract s, Ico_subset_Icc_self hs_frac_mem, rfl⟩
    have ht_in_edge : poly.edgePath R tindex (Int.fract t) ∈ poly.edgeSet R tindex := by
      rw [edgeSet_eq_image_edgePath]
      exact ⟨Int.fract t, Ico_subset_Icc_self ht_frac_mem, rfl⟩
    have hp_in_both : poly.edgePath R sindex (Int.fract s) ∈
        poly.edgeSet R sindex ∩ poly.edgeSet R tindex := by
      rw [heq]
      exact ⟨by rw [← heq]; exact hs_in_edge, ht_in_edge⟩
    -- Step 3: Case split on adjacency
    by_cases hadj1 : tindex = sindex + 1
    · -- Adjacent case: tindex = sindex + 1
      -- Intersection is {poly (sindex + 1)}
      have hinter := h.adjacent_inter sindex
      rw [hadj1] at hp_in_both
      rw [hinter] at hp_in_both
      -- So the point equals poly (sindex + 1)
      simp only [mem_singleton_iff] at hp_in_both
      -- But edgePath at fract s = poly (sindex + 1) requires fract s = 1
      -- edgePath at 1 gives the endpoint
      have h1 : poly.edgePath R sindex 1 = poly (sindex + 1) := lineMap_apply_one ..
      have heq' : poly.edgePath R sindex (Int.fract s) = poly.edgePath R sindex 1 :=
        hp_in_both.trans h1.symm
      have : Int.fract s = 1 := lineMap_injective R (nde sindex) heq'
      -- This contradicts fract s < 1
      exact absurd this (ne_of_lt (Int.fract_lt_one s))
    · by_cases hadj2 : sindex = tindex + 1
      · -- Adjacent case: sindex = tindex + 1
        have hinter := h.adjacent_inter tindex
        rw [← hadj2] at hinter
        rw [Set.inter_comm] at hp_in_both
        rw [hinter] at hp_in_both
        simp only [mem_singleton_iff] at hp_in_both
        -- The point equals poly sindex = poly (tindex + 1)
        -- On edge tindex, this is at parameter 1, so fract t = 1
        have h1 : poly.edgePath R tindex 1 = poly (tindex + 1) := lineMap_apply_one ..
        have hvertex : poly.vertices sindex = poly.vertices (tindex + 1) := by rw [hadj2]
        have heq' : poly.edgePath R tindex (Int.fract t) = poly.edgePath R tindex 1 := by
          rw [h1, ← hvertex, ← hp_in_both, ← heq]
        have : Int.fract t = 1 := lineMap_injective R (nde tindex) heq'
        exact absurd this (ne_of_lt (Int.fract_lt_one t))
      · have hdisj := h.nonadjacent_disjoint hindex hadj1 hadj2
        exact (Set.disjoint_iff.mp hdisj hp_in_both).elim

theorem boundaryMap_range (h : poly.IsSimple R) (nde : poly.HasNondegenerateEdges) :
    Set.range (poly.boundaryMap (R := R)) = poly.boundary R := by
  sorry

end IsSimple

end Polygon
