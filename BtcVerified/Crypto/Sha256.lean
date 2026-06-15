import BtcVerified.Crypto.Collision
/-!
  # SHA-256 and Bitcoin's double-SHA-256

  A concrete, computable implementation of SHA-256 (FIPS 180-4) over byte
  strings, and Bitcoin's `SHA256d = SHA256 ∘ SHA256`. These are ordinary
  reducible `def`s — not abstract or `opaque` — so a digest *computes*: merkle
  roots, txids, and block hashes can be evaluated and checked by reduction
  (`decide`/`#eval`/`native_decide`) against real chain data.

  Collision-resistance is **not** stated here. It is unprovable for a concrete
  hash (an infinite domain into `BitVec 256` has collisions by pigeonhole, so
  injectivity is provably false and cannot be assumed without inconsistency).
  Where a soundness proof needs it, it is carried as a hypothesis over an
  abstract hash — never as an axiom over this function.

  The implementation works on 32-bit words (`UInt32`) exactly as the standard
  specifies: big-endian word packing, the standard padding, message schedule,
  and compression. It is validated against the published test vectors in
  `Tests`.
-/

namespace BtcVerified.Sha256

/-- SHA-256 round constants `K[0..63]` (first 32 bits of the fractional parts of
the cube roots of the first 64 primes). -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- SHA-256 initial hash value `H[0..7]` (first 32 bits of the fractional parts
of the square roots of the first 8 primes). -/
def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotate a 32-bit word right by `n` bits. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Pack four bytes into a big-endian 32-bit word. -/
@[inline] def beWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

/-- Unpack a 32-bit word into its four big-endian bytes. -/
@[inline] def wordBytes (w : UInt32) : List UInt8 :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- Unpack a 64-bit word into its eight big-endian bytes. -/
def word64Bytes (w : UInt64) : List UInt8 :=
  [(w >>> 56).toUInt8, (w >>> 48).toUInt8, (w >>> 40).toUInt8, (w >>> 32).toUInt8,
   (w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- Pad a message to a multiple of 64 bytes: append `0x80`, then zero bytes, then
the 64-bit big-endian bit length. -/
def pad (msg : List UInt8) : List UInt8 :=
  let len := msg.length
  let zeros := (64 - (len + 9) % 64) % 64
  msg ++ 0x80 :: List.replicate zeros 0x00 ++ word64Bytes (UInt64.ofNat (len * 8))

/-- The SHA-256 compression function: fold a 16-word message block into the
current 8-word hash state. -/
def compress (state block : Array UInt32) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    w := w.set! i block[i]!
  for i in [16:64] do
    let w15 := w[i - 15]!
    let w2 := w[i - 2]!
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := h + s1 + ch + roundConstants[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
           state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- The big-endian 32-bit words of a byte array (length assumed a multiple of 4). -/
def toWords (bytes : Array UInt8) : Array UInt32 := Id.run do
  let mut ws : Array UInt32 := Array.mkEmpty (bytes.size / 4)
  for i in [0:bytes.size / 4] do
    ws := ws.push (beWord bytes[4 * i]! bytes[4 * i + 1]! bytes[4 * i + 2]! bytes[4 * i + 3]!)
  return ws

/-- The final 8-word hash state of SHA-256: pad, split into 16-word blocks,
and fold each through the compression function. -/
def sha256State (msg : List UInt8) : Array UInt32 := Id.run do
  let words := toWords (pad msg).toArray
  let mut state := initialHash
  for b in [0:words.size / 16] do
    let mut block : Array UInt32 := Array.replicate 16 0
    for j in [0:16] do
      block := block.set! j words[16 * b + j]!
    state := compress state block
  return state

/-- The 32-byte digest of an 8-word hash state: each word unpacked big-endian,
in order. Kept outside the state loop so the digest's byte length is a
structural fact rather than a property of an imperative fold. -/
def stateBytes (s : Array UInt32) : List UInt8 :=
  wordBytes s[0]! ++ wordBytes s[1]! ++ wordBytes s[2]! ++ wordBytes s[3]!
    ++ wordBytes s[4]! ++ wordBytes s[5]! ++ wordBytes s[6]! ++ wordBytes s[7]!

/-- SHA-256 of a byte string: the 32-byte digest. -/
def sha256 (msg : List UInt8) : List UInt8 := stateBytes (sha256State msg)

/-- Bitcoin's double-SHA-256: `SHA256(SHA256(msg))`. The hash behind txids,
block hashes, and merkle nodes. -/
def sha256d (msg : List UInt8) : List UInt8 := sha256 (sha256 msg)

/-- A SHA-256 digest is exactly 32 bytes. -/
theorem sha256_length (msg : List UInt8) : (sha256 msg).length = 32 := by
  simp [sha256, stateBytes, wordBytes]

/-- A double-SHA-256 digest is exactly 32 bytes. -/
theorem sha256d_length (msg : List UInt8) : (sha256d msg).length = 32 :=
  sha256_length _

/-- Two distinct byte strings with the same double-SHA-256 digest. Theorems
about hash commitments conclude with this as a constructive disjunct — never
assuming its absence as an axiom, which would be inconsistent for a concrete
hash (an infinite domain into 32 bytes has collisions by pigeonhole). The
*intractability* of producing a witness is the consumer's hypothesis. -/
abbrev Collision : Prop := BtcVerified.Collision sha256d

/-- Bitcoin's double hashing inherits collision resistance from `sha256`: a
`sha256d` collision is a `sha256` collision (in the outer call if the inner
digests differ, in the inner call otherwise), so resistance of `sha256` gives
resistance of `sha256d = sha256 ∘ sha256`. -/
theorem collisionResistant_sha256d (h : CollisionResistant sha256) :
    CollisionResistant sha256d :=
  h.comp h

/-- The converse: a `sha256d` collision forces a `sha256` collision in the inner
call, so resistance of `sha256d` gives resistance of `sha256`. Together with
`collisionResistant_sha256d`, the two resistances are equivalent. -/
theorem collisionResistant_sha256_of_sha256d (h : CollisionResistant sha256d) :
    CollisionResistant sha256 :=
  CollisionResistant.of_comp (f := sha256) (g := sha256) h

/-- Collision resistance of `sha256` and of `sha256d` are equivalent. -/
theorem collisionResistant_sha256_iff_sha256d :
    CollisionResistant sha256 ↔ CollisionResistant sha256d :=
  ⟨collisionResistant_sha256d, collisionResistant_sha256_of_sha256d⟩

end BtcVerified.Sha256
