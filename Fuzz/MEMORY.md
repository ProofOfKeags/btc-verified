# Memory-lifetime contract for the transaction harness

Leak checking is part of the harness's resource-correctness evidence. Its
purpose is to detect lost ownership of temporary objects while allowing
explicitly justified process-lifetime state. It is not a performance target.
The process may own fixed runtime state until the operating system reclaims
its address space at exit; transaction inputs, intermediate values, and
observations do not acquire that lifetime merely because Lean allocated them.

## Admission criteria

An exemption requires all of the following:

1. **Identity and ownership:** identify the allocation or a precisely defined
   allocation class, its owning object, and the source-backed reason it must
   remain alive for the process lifetime.
2. **A bound independent of campaign history:** explain why retained storage
   does not grow without bound as more transactions or distinct inputs are
   processed. A fixed set of fixed-size closed constants qualifies. A cache
   without an independently justified bound does not.
3. **Narrow scope:** annotate the identified live object at its lifetime
   transition. Do not disable detection around initialization, observation, or
   another whole call; those calls can allocate ordinary temporaries too.
   Do not suppress every stack containing `lean_obj_once_cold`, a GMP
   allocator, or another common runtime function.
4. **Reachability review:** account for objects reachable from the exempt
   object, including external payloads and later mutations. LeakSanitizer
   treats allocations reachable from an ignored object as exempt too. A
   process-lifetime mutable root can therefore conceal input-dependent growth.
5. **Recorded provenance:** record the source revision, source locations,
   ownership argument, bound, and checks exercising the relevant boundary.
   Changes to the toolchain, allocator configuration, imports, or annotation
   sites require renewed review.

The detector finding an allocation, its small size, a stable observed RSS, or
its allocation during startup is insufficient justification. A new unexplained
report is a failure to investigate, not a reason to expand an allowlist.
Changing an ordinary allocation to persistent solely to silence a report is
also disallowed.

These rules apply to upstream annotations as well as annotations maintained in
this repository. Upstream persistence is evidence of intended lifetime; it
does not establish the application-level bound by itself.

## Pinned Lean lifetime mechanism

This audit concerns Lean `v4.30.0-rc2`, commit
`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, as selected by
[`../lean-toolchain`](../lean-toolchain).

Lean documents `Runtime.markPersistent` as making a value and its object graph
live until process exit
([contract](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Init/System/IO.lean#L1860-L1871)).
In the runtime, `lean_mark_persistent` traverses the graph, removes normal
reference counting, and, when compiled with AddressSanitizer, calls
`__lsan_ignore_object` on each newly persistent object
([implementation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/runtime/object.cpp#L532-L555)).
This is an object-lifetime annotation, not a period during which every
allocation is ignored. Temporaries allocated and abandoned while constructing
the persistent result are not automatically annotated by that transition.

For generated lazy closed values, `lean_obj_once_cold` stores the initialized
result in its once-cell location and marks that result persistent
([implementation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/runtime/object.cpp#L2799-L2807)).
This mechanism explains the lifetime of a fixed closed value. It does not
authorize arbitrary uses of persistence for transaction-derived values.

### Identified allocations and remaining limits

- **`CountedList.ofList?`'s `2^64` bound:** the specification uses a fixed bound
  independent of its input list
  ([definition](../BtcVerified/Serialize/CountedList.lean)). With the pinned
  compiler, `.lake/build/ir/BtcVerified/Serialize/CountedList.c` contains a
  static once cell and an initializer calling
  `lean_cstr_to_nat("18446744073709551616")`. Its result is obtained through
  `lean_obj_once`. The bound is one immutable integer per generated closed
  constant, not one retained integer per transaction. Its process-lifetime
  annotation meets the policy. Regenerate and inspect this code when the
  compiler or definition changes.
- **Startup numeric constants:** the original symbolized report includes
  signed-integer bounds and `Lean.PersistentArray.tooBig` among GMP allocation
  paths. The latter is the platform-dependent fixed value `USize.size / 8`
  ([definition](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/PersistentArray.lean#L140-L146)).
  Fixed closed numeric results can use the same persistence justification.
  A GMP allocation's stack alone does not establish that it is the retained
  result rather than a leaked intermediate. No GMP-wide exemption is allowed.
- **Startup mutex payloads:** `lean_io_basemutex_new` allocates a native mutex
  owned by a Lean external object; normal finalization deletes that payload
  ([ownership](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/runtime/mutex.cpp#L15-L27)).
  The original report traces allocations through fixed Lean server globals
  such as `eligibleHeaderDeclsMutex`
  ([initializer](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Completion/EligibleHeaderDecls.lean#L28-L29))
  and handler registration
  ([allocation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Requests.lean#L648-L659)).
  A fixed persistent wrapper can justify retaining its mutex. The contents of
  mutable server state have no blanket exemption: the transaction harness does
  not execute these server handlers, and adding such execution would require
  a new reachability and growth review.

The historical Linux diagnostic reported 264 bytes in 16 allocations on an
empty replay and 280 bytes in 17 allocations after the small regressions
([diagnostic run](https://github.com/ProofOfKeags/btc-verified/actions/runs/35390786709/job/105748400684)).
Those totals locate the original issue; they are neither an allowed leak
budget nor an item-by-item proof that every startup allocation is legitimate.
Only allocations covered by justified lifetime transitions are exempt.

## Allocator visibility and instrumentation

The detector must see the Lean object that owns an external allocation.
Instrumenting only the C++ harness while using an opaque allocator for Lean
objects does not establish this. In particular, an invisible Lean wrapper can
make its live GMP or mutex payload appear unowned, while allocator pools can
also conceal genuinely abandoned Lean objects.

The pinned Lean project's own `sanitize` preset instruments runtime C++,
generated C, and linking, and disables both `SMALL_ALLOCATOR` and
`USE_MIMALLOC`
([preset](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/CMakePresets.json#L34-L47)).
The check must record and validate the actual allocator and runtime used.
Merely adding a sanitizer to the final link does not instrument prebuilt Lean
libraries. A platform without supported leak instrumentation can provide
semantic-conformance evidence, but must report leak checking as unavailable
rather than passed.

## Controls and interpretation

The memory check requires a negative control separate from semantic mismatch
injection. It must abandon an ordinary dynamically allocated Lean object on
the observation path while the normal persistence annotations remain enabled.
The chosen result is a `ByteArray`/scalar-array object: `lean_alloc_sarray`
allocates its header and byte capacity together through one `lean_alloc_object`
call ([pinned representation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/include/lean/lean.h#L1002-L1018)).
Consequently this injection's contract is exactly one direct allocation and no
indirect graph; changing the injected type requires reviewing that assertion.
The child process must fail specifically with a LeakSanitizer report identifying
the injected allocation. An arbitrary crash is insufficient. Retain the
input, command, environment, toolchain identity, exit status, and complete log
needed to replay both the clean and injected cases.

The clean counterpart must pass. A control that detects only a C++ `malloc`
leak does not demonstrate visibility into Lean allocations. The injection
must also be exercised in a fresh child process so retained stack or register
references from the controller do not defeat the intended test.

Passing these controls supports the detector's sensitivity at the tested
boundary. It does not prove all allocations are visible, all paths are leak
free, or all persistent state is bounded. Repeated-input retention checks can
provide additional evidence, but do not replace ownership review or establish
a bound by themselves. Semantic agreement and memory-lifetime checks remain
separate claims in the saved run evidence.
