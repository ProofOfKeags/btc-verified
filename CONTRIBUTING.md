# Contributing

Contributions are welcome. The bar is the one the repo already sets for
itself: small, legible proof leaves that build cleanly and state exactly what
they prove.

## Ground rules

- **No `sorry` on master.** CI's axiom audit (`Tests/AxiomAudit.lean`) fails
  the build if a registered theorem depends on `sorryAx` or any axiom outside
  `propext`, `Classical.choice`, `Quot.sound`.
- **Linter-clean.** `lake lint` runs the mathlib standard linter set and must
  pass.
- **Every public declaration is documented.** Files carry a `/-!` module
  header explaining the design and listing checked claims; declarations carry
  `/--` doc-strings.
- **Naming** follows mathlib conventions: `UpperCamelCase` types and
  predicates, `lowerCamelCase` defs, conclusion-describing theorem names.
  Bitcoin's own nomenclature (`scriptSig`, `nBits`, `vout`) is kept verbatim.
- **One type per module**: a module defines at most one `structure`/`inductive`,
  with its instances alongside it (see `CLAUDE.md` for the exact rule and its
  two exceptions).

## Workflow

With Nix installed, enter the development shell first:

```sh
nix develop
```

Then run the normal Lean workflow:

```sh
lake exe cache get   # once, after cloning or bumping mathlib
lake build           # builds the library and the tests
lake test            # real blocks through the block codec (fetched on first run, cached)
lake lint
```

A new proof leaf should:

1. live in its own module, imported from `BtcVerified.lean`;
2. register its headline theorems in `Tests/AxiomAudit.lean`;
3. add a golden vector if it decodes real wire bytes — inline in
   `Tests/GoldenVectors.lean`, or as a fetched fixture in
   `Tests/BlockFixtures.lean` when the bytes run to kilobytes (downloaded on
   first `lake test`, cached gitignored, never committed);
4. get a section in `README.md` under "Current proof leaves" — what it is,
   `Checked claims:` naming the theorems, and why it matters.

Commit messages are imperative-mood with a body explaining the why; see
`git log` for the house style.

## Finding lemmas by type

Mathlib names are transcriptions of the statement (the head symbols of the
left-hand side, read outside-in, joined by `_`, with relation/connective/
direction words), so a name is meant to be *reconstructed* from the type
rather than memorized — see the [naming
guide](https://leanprover-community.github.io/contribute/naming.html). When
reconstruction fails, search by type:

- **`exact?` / `apply?` / `rw?`** — built into Lean + Mathlib, zero setup:
  place the cursor on the goal and they search for a lemma matching its type.
  The day-to-day tool.
- **loogle** — search by term *pattern/shape*, e.g. `List.zipWith (_ + _)`:
  the web UI at <https://loogle.lean-lang.org/>, or the `#loogle` command
  in-editor.
- **`#leansearch`** — natural-language queries (<https://leansearch.net>) via
  LeanSearchClient, which this project already depends on, so it works in any
  file here.

## Deferring work

If you set work aside, file a GitHub issue for it — a deferral is not done
until it is tracked. See the policy in `CLAUDE.md`.

See `CLAUDE.md` for the full design conventions (the codec discipline, the
spec/transport split, doc-string formatting).
