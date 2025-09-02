/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.MerkleTree.Defs

/-!
# Inductive Merkle Tree Extractibility

-/


namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type}

def populate_down_tree {α : Type} (s : Skeleton)
    (children : α → (α × α))
    (root : α) :
    FullData α s :=
  match s with
  | .leaf => FullData.leaf root
  | .internal s_left s_right =>
    let ⟨left_root, right_root⟩ := children root
    FullData.internal
      root
      (populate_down_tree s_left children left_root)
      (populate_down_tree s_right children right_root)

/--
The extraction algorithm for Merkle trees.

This algorithm takes a merkle tree cache, a root, and a skeleton, and
returns (optionally?) a FullData of Option α.

* It starts with the root and constructs a tree down to the leaves.
* If a node is not in the cache, its children are None
* If a node is in the cache twice (a collision), its children are None
* If a node is None, its children are None
* Otherwise, a nodes children are the children in the cache.


TODO, if there is a collision, but it isn't used or is only used in a subtree,
should the rest of the tree work? Or should it all fail?
-/
def extractor {α : Type} (s : Skeleton)
  (cache : List ((α × α) × α))
  (root : α) :
  FullData (Option α) s := sorry



end InductiveMerkleTree
