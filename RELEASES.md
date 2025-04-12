
# timelib releases

v0.2.0
----------

+ Bump lean version to leanprover/lean4:v4.19.0-rc2

+ Remove mathlib dependency. Most of what's needed for this library can now be done with core only. Proofs and class implementations that still need mathlib (e.g. LinearOrder, some of the proofs about heterogeneous comparisons) can be implemented as a separate library.

+ Complete lemmas showing validity of Date conversions (Scalar <-> Ordinal <-> Ymd). Leans heavily on the `omega` tactic, but still requires a significant amount of baby sitting. These proofs may become significantly shorter when the `grind` tactic is available. In hindsight, the conversion functions should have been written with right-biased bracketing (e.g. `a + (b + c)`) to eliminate the need for many of the associativity rewrites, which require verbose type annotations. In any case, the intermediate lemmas and case branches are now known, so a future rewrite with stronger tactics is feasible.

+ Specify and implement leap seconds. Uses a list of leap seconds and a well-formedness predicate.

+ Add ISO 8601 date time parsing w/ initial leap second and time zone support

+ More consistent namespacing
