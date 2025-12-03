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

/--
Convert a computation to one that also returns its query log

TODO
- generalize Type universe?
- generalize spec
- move to vcv?
- already in vcv?
-/
def OracleComp.withLogging {T : Type} (spec : OracleSpec Unit) (oa : OracleComp (spec) T) :
    OracleComp (spec) (T × (spec).QueryLog) :=
  (simulateQ loggingOracle oa).run

/--
prove that logging of a bind is bind of loggings.
-/
lemma OracleComp.pure_withLogging (A B) (spec : OracleSpec Unit)
    (oa : OracleComp (spec) A) (ob : A → OracleComp (spec) B) :
    (oa >>= ob).withLogging =
    do
      let (a, a_log) ← oa.withLogging
      let (b, b_log) ← (ob a).withLogging
      return (b, a_log ++ b_log) := by
  sorry

/--
prove that logging of a bind is bind of loggings.
-/
lemma OracleComp.bind_withLogging (A B) (spec : OracleSpec Unit)
    (oa : OracleComp (spec) A) (ob : A → OracleComp (spec) B) :
    (oa >>= ob).withLogging =
    do
      let (a, a_log) ← oa.withLogging
      let (b, b_log) ← (ob a).withLogging
      return (b, a_log ++ b_log) := by
  sorry

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
The game for extractability.
-/
def extractability_game
    [DecidableEq α] [SelectableType α] [Fintype α] [(spec α).FiniteRange]
    {s : Skeleton}
    {AuxState : Type}
    (committingAdv : OracleComp (spec α)
        (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α) (SkeletonLeafIndex s × α × List α)) :
    OracleComp (spec α)
      (α × AuxState × SkeletonLeafIndex s × α × List α ×
       FullData (Option α) s × List (Option α) × Bool) :=
  do
    let ((root, aux), queryLog) ← committingAdv.withLogging
    let extractedTree := extractor s queryLog root
    let (idx, leaf, proof) ← openingAdv aux
    let extractedProof := generateProof extractedTree idx
    let verified ← verifyProof idx leaf root proof
    return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified)



/--
The game for extractability, augmented to return the query logs
of the committing adversary, opening adversary, and verification.
-/
def extractability_game_with_logging
    [DecidableEq α] [SelectableType α] [Fintype α] [(spec α).FiniteRange]
    {s : Skeleton}
    {AuxState : Type}
    (committingAdv : OracleComp (spec α)
        (α × AuxState))
    (openingAdv : AuxState →
        OracleComp (spec α) (SkeletonLeafIndex s × α × List α)) :
    OracleComp (spec α)
      (α × AuxState × SkeletonLeafIndex s × α × List α ×
       FullData (Option α) s × List (Option α) × Bool ×
       (spec α).QueryLog × (spec α).QueryLog × (spec α).QueryLog)
         :=
  do
    let ((root, aux), committingLog) ← (committingAdv).withLogging
    let extractedTree := extractor s committingLog root
    let ((idx, leaf, proof), openingLog) ← ((openingAdv aux)).withLogging
    let extractedProof := generateProof extractedTree idx
    let (verified, verificationLog) ←
      ((verifyProof idx leaf root proof)).withLogging
    return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
            committingLog, openingLog, verificationLog)




-- Does this exists in vcvio somewhere?
def collisionIn {α : Type} [DecidableEq α]
    (log : (spec α).QueryLog) : Prop :=
  ∃ q1 q2, (q1 ≠ q2) ∧
    q1 ∈ log.getQ () ∧ q2 ∈ log.getQ () ∧
    q1.2 == q2.2



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

Here, we loosen this a bit to attempt a proof by considering all collisions
in the combined query logs of the committing and opening adversaries and the verification.
-/
theorem extractability [DecidableEq α] [SelectableType α] [Fintype α] [(spec α).FiniteRange]
    {s : Skeleton}
    {AuxState : Type}
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
    [fun (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified) =>
        verified ∧
        (not (leaf == extractedTree.get idx.toNodeIndex)
        ∨ not (proof.map (Option.some) == extractedProof)) |
      do
        let (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified) ←
          extractability_game committingAdv openingAdv
        return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified)
      ] ≤
        1/2 * ((qb + s.depth) - 1) * (qb + s.depth) / (Fintype.card α)
        + 2 * (s.depth + 1) * s.leafCount / (Fintype.card α)
    := by

  calc
    -- We first rewrite the game to include the query logs
    _ = [fun (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
              committingLog, openingLog, verificationLog) =>
            verified ∧
            (not (leaf == extractedTree.get idx.toNodeIndex)
            ∨ not (proof.map (Option.some) == extractedProof)) |
          do
            let (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                committingLog, openingLog, verificationLog) ←
              extractability_game_with_logging committingAdv openingAdv
            return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                    committingLog, openingLog, verificationLog)] := by
      -- This follows from marginalization
      sorry
    -- The bad event happens only when there is a collision event
    -- or the bad event happens with no collision
    _ ≤ [fun (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
            committingLog, openingLog, verificationLog)
            =>
            (collisionIn (committingLog ++ openingLog ++ verificationLog)) ∨
            (¬ (collisionIn (committingLog ++ openingLog ++ verificationLog)) ∧
            (verified ∧
            (not (leaf == extractedTree.get idx.toNodeIndex)
            ∨ not (proof.map (Option.some) == extractedProof)))) |
          do
            let (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                committingLog, openingLog, verificationLog) ←
              extractability_game_with_logging committingAdv openingAdv
            return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                    committingLog, openingLog, verificationLog)] := by
      apply probEvent_mono
      tauto
    -- We apply the union bound
    _ ≤ [fun (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
            committingLog, openingLog, verificationLog)
            =>
            (collisionIn (committingLog ++ openingLog ++ verificationLog)) |
          do
            let (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                committingLog, openingLog, verificationLog) ←
              extractability_game_with_logging committingAdv openingAdv
            return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                    committingLog, openingLog, verificationLog)] +
        [fun (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
            committingLog, openingLog, verificationLog)
            =>
            (¬ (collisionIn (committingLog ++ openingLog ++ verificationLog)) ∧
            (verified ∧
            (not (leaf == extractedTree.get idx.toNodeIndex)
            ∨ not (proof.map (Option.some) == extractedProof)))) |
          do
            let (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                committingLog, openingLog, verificationLog) ←
              extractability_game_with_logging committingAdv openingAdv
            return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                    committingLog, openingLog, verificationLog)] := by
        -- TODO is this in vcvio somewhere?
        sorry
    -- We bound the collision event probability with a collision bound
    _ ≤ 1/2 * ((qb + s.depth) - 1) * (qb + s.depth) / (Fintype.card α) +
        [fun (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
            committingLog, openingLog, verificationLog)
            =>
            (¬ (collisionIn (committingLog ++ openingLog ++ verificationLog)) ∧
            (verified ∧
            (not (leaf == extractedTree.get idx.toNodeIndex)
            ∨ not (proof.map (Option.some) == extractedProof)))) |
          do
            let (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                committingLog, openingLog, verificationLog) ←
              extractability_game_with_logging committingAdv openingAdv
            return (root, aux, idx, leaf, proof, extractedTree, extractedProof, verified,
                    committingLog, openingLog, verificationLog)] := by
        gcongr
        -- TODO: Prove a general collision bound lemma
        sorry
    -- We bound the no-collision bad event probability
    _ ≤ 1/2 * ((qb + s.depth) - 1) * (qb + s.depth) / (Fintype.card α) +
        2 * (s.depth + 1) * s.leafCount / (Fintype.card α):= by
        sorry


  /-
  Now we can break down the bad event into smaller events
  In the SNARGS book, they define
  E_col = the event that there is a collision in committingLog
  E_tree = the event that the tree extraction with committingLog
           is different from the tree extraction
           with the combined committingLog and openingLog
  E_sub = the event that The verificationLog contains a query to a node not in the committingLog
          and verification succeeds

  The SNARGs book makes the observation that

  Pr[Adversary wins] ≤ Pr[E_col]
                       + Pr[E_tree | not E_col]
                       + Pr[E_sub | not E_col and not E_tree]
                       + Pr[Adversary wins | not E_col and not E_tree and not E_sub]

  But I think this really stands in for the tighter version, which might be easier to reason about.

  Pr[Adversary wins] ≤ Pr[E_col]
                       + Pr[E_tree and not E_col]
                       + Pr[E_sub and not E_col and not E_tree]
                       + Pr[Adversary wins and not E_col and not E_tree and not E_sub]

  TODO: does the proof really have to be this complicated?
  Can't we simply look at the event of any collision at all happening?

  * Does a collision happen in the adversary's queries and verification combined?
    * Probability of YES is small by query bound
    * If not, then consider whether the index opened exists in the extracted tree.
      * If yes, then if the proof differs at all, we must leave the extracted tree
        * After which, we can't return without a collision, so we don't verify.
      * If no, then the only way to verify is to have a collision.

  -/


end InductiveMerkleTree
