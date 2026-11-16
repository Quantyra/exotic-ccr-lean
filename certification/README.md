# Jacobian–Weyl certification maintenance

This branch implements Dan's 2026-11-10 request to complete three prioritized
certification recommendations. The work is **in progress and not certified**.
The historical publication freeze `2e40c4cab86a1ef97cb3334497d10081dfe33867`
and its theorem/audit source `fbcdd0345d2f2540cd537204be2178ae07e18a5e`
remain immutable. The science release `001035470f8ebfa180c840e507796aec560284b8`
is unchanged. No new publication or release is part of this work.

The selected obligations are:

1. Replay the original pinned build and nine-export audit, retain durable full
   logs, types and transitive axiom evidence, and broaden the claim map to A–F.
2. Prove the continuum lower bound for `SelfAdjointExtension H_X1_min` by
   composing the existing unit-phase injection with formal cardinality results.
3. Prove all-j analytic symmetry and the multiplication commutator from Theorem
   C(2) on the actual compactly supported smooth core, including domain
   preservation and correspondence with the canonical partial L² operators.

[argument.json](argument.json) gives the mathematical argument and acceptance
obligations. [claim-map.json](claim-map.json) separates exact exports,
alternative formal routes and paper-only boundaries. Its source inventory is
not proof acceptance: acceptance requires a successful admitted native build,
complete generated type/axiom audit and the applicable independent reviews.

The original CI success metadata remains accessible, but the cited artifact
returns HTTP 404, the run's artifact list is empty, and its logs return HTTP
410. Those observations establish an evidence-retention gap, not a proof
failure. The new replay will be recorded separately from the original run.

The pinned environment is Lean `4.33.0-rc1` (commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`) and Mathlib
`79d0395a1825a6264ad5d269e35e60537518955e`. Proof candidates use the guarded
Quietbox OProver deployment. The working-tree runner recognizes CPU-02 through
CPU-05 with exact runtime hostname matching. CPU-06 is excluded from compute.
Preflight requires zero memory
events except for the hash-bound CYINT qualifier profile on CPU-03: high=388
is admitted only when `approved_event_profile` matches boot
`82d42716-4868-43ae-b22e-52e55d5cbecf`, with all other counters zero. Its
authority is qualifier SHA-256
`655f591d36edf74d59c2f610b61c0e7009ad0cd3cb0b383e552a2c513439ea5f`. CPU-05's
parent `memory.events.high` metric is excluded from admission and continuous
event comparisons under Dan's 2026-11-15 direction; it remains recorded in
receipts. CPU-05 `max`, `oom` and `oom_kill` counters must remain zero and
unchanged. Other hosts retain the zero-event gate or their exact approved
profile. The continuous guard binds the host boot and all gated event counters.
For the same pinned CPU-03 admission, the host-specific deeper-refill profile
may reclaim only the dispatched service's own cgroup leaf, targeting 3.125 GiB
with an 800 MiB per-request cap; it cannot alter host-wide cgroup controls. The
full-project run still supplies the capacity evidence, with the existing
resource guard and pause/time ceilings. This narrow baseline exception does not
itself establish full-project campaign capacity.
Dan reassigned CPU-06 to the dedicated Kuzuryu notification service on
2026-11-15; it is excluded from compute and the runner rejects it. The CPU-05
full candidate v2 run on 2026-11-16 stopped while compiling `ExoticCCR.Basic`
because the delegated reclaim controller retained an independent hard-coded
32-request cap. The run had used 34 of its 64 allowed pauses and 33 reclaim
requests. The runner now binds the reclaim-request cap to the captured
`maximum_pauses` value (32 for legacy offers, 64 for v2, and 96 for v3);
the 180-second per-pause and 2,400-second aggregate limits are unchanged. The
v2 full build used all 64 pauses and 1,708.62 aggregate pause seconds before
its count budget stopped the run; the Lean build and audit remain incomplete.
The v3 candidate raises only the pause-count ceiling, leaving the aggregate,
per-pause and service ceilings unchanged. This controller policy change is
not itself build or certification evidence. Compilation
requires the existing exclusive lease,
worker identity and host-specific admission. The root free-space
threshold is captured as `root_free_threshold_bytes` in the hash-bound
admission; it defaults to 500 MiB (524,288,000 bytes) for this campaign and may
be raised, but not lowered. The preflight and continuous resource guard use the
same value, and a reserve breach stops the owned build cleanly. Inode, memory,
CPU, swap, task, source, toolchain, lease and provenance checks remain in force.
Windows does not run Lean, Lake or LSP.

Only `propext`, `Classical.choice` and `Quot.sound` are allowed in transitive
axiom dependencies. A new declaration may use a subset of those axioms; each
of the nine historical exports must preserve its original profile. The audit
also records fully elaborated types and exact source/control identities.

This maintenance does not certify every manuscript argument. Quantitative
cutoff norm bounds and global maximal-sheet packaging remain outside these
three recommendations. It does not establish the exact cardinality of the
entire extension type, essential self-adjointness or deficiency indices of
other operators, strong/exponentiated CCR, or any physical advantage claim.

Remaining work: successful baseline replay, completed and compiled new
declarations, expanded audit, durable evidence and independent reviews.
