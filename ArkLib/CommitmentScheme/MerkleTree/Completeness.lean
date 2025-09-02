/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.MerkleTree.Defs

/-!
# Inductive Merkle Tree Completeness

-/


namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

/--
A functional form of the completeness theorem for Merkle trees.
This references the functional versions of `getPutativeRoot` and `buildMerkleTree_with_hash`
-/
theorem functional_completeness (α : Type) {s : Skeleton}
  (idx : SkeletonLeafIndex s)
  (leaf_data_tree : LeafData α s)
  (hash : α → α → α) :
  (getPutativeRoot_with_hash
    idx
    (leaf_data_tree.get idx)
    (generateProof
      (buildMerkleTree_with_hash leaf_data_tree hash) idx)
    (hash)) =
  (buildMerkleTree_with_hash leaf_data_tree hash).getRootValue := by
  induction s with
  | leaf =>
    match leaf_data_tree with
    | LeafData.leaf a =>
      cases idx with
      | ofLeaf =>
        simp [buildMerkleTree_with_hash, getPutativeRoot_with_hash]
  | internal s_left s_right left_ih right_ih =>
    match leaf_data_tree with
    | LeafData.internal left right =>
      cases idx with
      | ofLeft idxLeft =>
        simp_rw [LeafData.get_ofLeft, LeafData.leftSubtree_internal, buildMerkleTree_with_hash,
          generateProof_ofLeft, FullData.rightSubtree, FullData.leftSubtree,
          getPutativeRoot_with_hash, left_ih, FullData.internal_getRootValue]
      | ofRight idxRight =>
        simp_rw [LeafData.get_ofRight, LeafData.rightSubtree_internal, buildMerkleTree_with_hash,
          generateProof_ofRight, FullData.leftSubtree, FullData.rightSubtree,
          getPutativeRoot_with_hash, right_ih, FullData.internal_getRootValue]


/--
Completeness theorem for Merkle trees.

The proof proceeds by reducing to the functional completeness theorem by a theorem about
the OracleComp monad,
and then applying the functional version of the completeness theorem.
-/
theorem completeness [DecidableEq α] [SelectableType α] {s}
    (leaf_data_tree : LeafData α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    (((do
      let cache ← buildMerkleTree leaf_data_tree
      let proof := generateProof cache idx
      let _ ← verifyProof idx (leaf_data_tree.get idx) (cache.getRootValue) proof
      ).simulateQ (randomOracle)).run preexisting_cache).neverFails := by
  -- An OracleComp is never failing on any preexisting cache
  -- if it never fails when run with any oracle function.
  revert preexisting_cache
  rw [randomOracle_neverFails_iff_runWithOracle_neverFails]
  -- Call this hash function `f`
  intro f
  -- Simplify
  simp_rw [verifyProof, guard_eq, bind_pure_comp, id_map', runWithOracle_bind,
    runWithOracle_buildMerkleTree, runWithOracle_getPutativeRoot]
  simp only [apply_ite, runWithOracle_pure, runWithOracle_failure, Option.bind_eq_bind,
    Option.bind_some, Option.isSome_some, Option.isSome_none, Bool.if_false_right, Bool.and_true,
    decide_eq_true_eq]
  exact functional_completeness α idx leaf_data_tree fun left right ↦ f () (left, right)

end InductiveMerkleTree
