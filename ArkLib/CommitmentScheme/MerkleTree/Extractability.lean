/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.MerkleTree.Defs

/-!
# Inductive Merkle Tree Extractability

-/

open scoped NNReal

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
  (cache : (spec α).QueryLog)
  (root : α) :
  FullData (Option α) s := sorry


/--
The extractability theorem for Merkle trees.

Adapting from the SNARGs book Lemma 18.5.1:

For any query bound `qb`,
and for any adversary `committingAdv` that outputs a root and auxiliary data
and any `openingAdv` that takes the auxiliary data and outputs a leaf index, leaf value, and proof,
such that committingAdv and openingAdv together obey the query bound `qb`.

If the `committingAdv` and `openingAdv` are executed, and the `extractor` algorithm is run on the
resulting cache and root from `committingAdv`,
then with probability at most κ
does simultaneously

* the merkle tree verification pass on the proof from `openingAdv`
* with the extracted leaf value not matching the opened leaf value or the adversary producing a proof different from the extracted proof.

Where κ is ≤ 1/2 * (qb - 1) * qb / (Fintype.card α)
        + 2 * (s.depth + 1) * s.leafCount / (Fintype.card α)
(For sufficiently large qb)
-/
theorem extractability [DecidableEq α] [SelectableType α] [Fintype α] [(spec α).FiniteRange]
    {s : Skeleton}
    (AuxState : Type)
    (committingAdv : OracleComp (spec α)
        (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α) (SkeletonLeafIndex s × α × List α))
    (qb : ℕ)
    (h_IsQueryBound_qb :
      IsQueryBound
        (do
          let (root, aux) ← committingAdv
          let (idx, leaf, proof) ← openingAdv aux
          pure ()) qb)
    (h_le_qb : 4 * s.leafCount + 1 ≤ qb)
          :
    [
      fun (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified) =>
        verified ∧
        (not (leaf == extractedTree.get idx.toNodeIndex)
        ∨ not (proof.map (Option.some) == extractedProof))
       |
      do
        let ((root, aux), queryLog) ← (simulateQ loggingOracle committingAdv).run
        let extractedTree := extractor s queryLog root
        let (idx, leaf, proof) ← openingAdv aux
        let extractedProof := generateProof extractedTree idx
        let verified ← verifyProof idx leaf root proof
        return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified)
      ] ≤
        1/2 * (qb - 1) * qb / (Fintype.card α)
        + 2 * (s.depth + 1) * s.leafCount / (Fintype.card α)
    := by

  sorry


end InductiveMerkleTree
