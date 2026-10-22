import BtcVerified.Consensus.UndoChecked
/-!
  # Transaction undo examples

  Synthetic state examples check captured coin contents, restoration from
  an independently assembled post-state, and the need for no-overwrite.
  They are model checks, not Bitcoin Core differential tests.
-/

namespace Tests.Undo

open BtcVerified

set_option linter.hashCommand false

private def emptyScript : Script := ⟨⟨[], by decide⟩⟩
private def lockingScript : Script := ⟨⟨[0x51], by decide⟩⟩
private def first : OutPoint := ⟨1, 0⟩
private def second : OutPoint := ⟨2, 3⟩
private def untouched : OutPoint := ⟨3, 0⟩
private def firstCoin : Coin := ⟨⟨7, lockingScript⟩, ⟨9, true⟩⟩
private def secondCoin : Coin := ⟨⟨5, emptyScript⟩, ⟨120, false⟩⟩
private def untouchedCoin : Coin := ⟨⟨42, lockingScript⟩, ⟨8, false⟩⟩

private def body : TxBody :=
  ⟨1, ⟨[⟨first, emptyScript, 0xffffffff⟩, ⟨second, emptyScript, 0xffffffff⟩],
      by decide⟩,
    ⟨[⟨8, lockingScript⟩, ⟨3, emptyScript⟩], by decide⟩, 0⟩

private def before : UtxoSet :=
  ((∅ : UtxoSet).insert first firstCoin).insert second secondCoin
    |>.insert untouched untouchedCoin

private def afterState : UtxoSet :=
  ((∅ : UtxoSet).insert untouched untouchedCoin)
    |>.insert ⟨body.txid, 0⟩ ⟨⟨8, lockingScript⟩, ⟨200, false⟩⟩
    |>.insert ⟨body.txid, 1⟩ ⟨⟨3, emptyScript⟩, ⟨200, false⟩⟩

-- Capturing retains both original scripts, amounts, heights, and flags.
#guard (TxUndo.capture before body).spentCoins = [(first, firstCoin), (second, secondCoin)]
#guard before.apply ⟨200, false⟩ body = afterState
#guard afterState.undo body (TxUndo.capture before body) = before

-- Removing a spent coin makes capture omit it; it does not invent a coin.
#guard (TxUndo.capture (before.erase second) body).spentCoins = [(first, firstCoin)]

-- The record cannot recover an overwritten, unspent output. This state
-- violates the round-trip theorem's freshness premise.
private def overwritingBefore : UtxoSet := before.insert ⟨body.txid, 0⟩ untouchedCoin

#guard (overwritingBefore.apply ⟨200, false⟩ body).undo body
    (TxUndo.capture overwritingBefore body) ≠ overwritingBefore

end Tests.Undo
