# Formal Verification POC: Theatrical Players Refactoring Kata

This POC demonstrates **Zero-Drift Legacy Java Modernization** using **Quint** and **Dafny** on Martin Fowler's *Theatrical Players Refactoring Kata*.

When modernizing legacy Java systems **without a domain SME** and **without changing the database schema**, traditional `.md` specification files cannot verify anything or catch subtle behavioral drift. Instead, we extract the exact behavioral semantics of the legacy [`StatementPrinter.java`](src/main/java/theatricalplays/StatementPrinter.java) into formal models and mathematically prove 100% equivalence with [`ModernStatementPrinter.java`](src/main/java/theatricalplays/ModernStatementPrinter.java).

---

## Comparison of 4 Formal Verification Tools for Legacy Java Modernization

| Dimension | **Quint** | **Dafny** | **Z3 (Python/Java API)** | **Lean 4** |
| :--- | :--- | :--- | :--- | :--- |
| **Core Mental Model** | **State Machine & Actions** (Models DB tables & state transitions over time) | **Verified OOP & Functional Code** (Methods with `requires`, `ensures`, `invariant`) | **Pure SMT Constraint Solver** (Math & logic formulas in Python/Java scripts) | **Pure Functional Language & Interactive Theorem Prover** (Dependent types & tactics) |
| **Syntax Feel** | TypeScript / Kotlin / Rust | Java / C# | Python / Java library calls | Haskell / ML + Mathematical proofs |
| **Readability as a Domain Spec (Replacing `.md`)** | **Very High** — Cleanest syntax for business workflows, invariants, and state transitions | **High** — Reads like typed domain classes/functions with formal contracts | **Low–Medium** — Looks like solver AST scripts rather than domain documentation | **High (for FP)** — Clean algebraic data types, though tactic proofs look mathematical |
| **Closeness to Legacy Java** | **Medium** — Models stateful mutations via `action`s, abstracts away low-level Java types | **Very High** — Supports classes, `while` loops, mutable variables, and compiles to `.jar` | **Medium** — Used externally via scripts to compare old vs. new branching logic | **Low–Medium** — Strictly pure functional; imperative loops must be modeled recursively/monadically |
| **Proof Effort** | **Zero** — 100% push-button via randomized simulation (`quint run`) + Z3/Apalache (`quint verify`) | **Low–Medium** — 90% automatic via Z3; requires loop `invariant`s and occasional `lemma`s for collections | **Zero** — 100% automatic via `solver.check()` (`unsat` = proven equivalent) | **Medium–High** — Requires tactic scripts (`by unfold ... split ... omega`), though decision tactics help |
| **Handling Loops & Collections** | Bounded unfolding (`foldl` over bounded lists/maps) | **Unbounded Deductive Proof** (Proves `while` loops over arbitrary-length `seq<T>`) | Hard (requires manual loop unrolling or quantifier tuning) | **Unbounded Inductive Proof** (Structural induction over lists/trees) |
| **Counterexamples When a Bug Exists** | **Best-in-Class** — Prints full step-by-step execution trace (`Init -> Step 1 -> Violation`) | **Good** — Reports failing postcondition/assertion and Z3 counterexample model | **Instant** — Prints exact variable assignment (`s.model()`) where `Legacy != Modern` | Via `Plausible` property-based testing library before attempting proof |
| **Compiles to Java / Test Generation** | Exports JSON execution traces (ITF) to replay in JUnit | **Compiles directly to `.java` / `.jar`** (`dafny build --target:java`) | Generates concrete JUnit test vectors directly from solver models | Compiles to native C binary; used as differential test oracle (e.g., AWS Cedar) |
| **Best Fit in Modernization** | **Multi-step workflows, DB table invariants, and stateful lifecycles** | **Complex methods, loops, domain calculations, and Java-native specs** | **Fast equivalence checking of gnarled `if/else` branching rules** | **Deep functional domain modeling & long-lived mathematical theorems** |

### Why We Selected **Quint** + **Dafny** for This POC
* **Quint** gives the **lowest-friction living specification** with instant step-by-step counterexample traces and zero manual proof writing.
* **Dafny** gives **unbounded mathematical guarantees** over imperative Java `while`/`for` loops and compiles directly to `.java`.

---

## Project Structure

* **Java Application (`src/` and `java/src/`)**
  * [`Play.java`](src/main/java/theatricalplays/Play.java), [`Performance.java`](src/main/java/theatricalplays/Performance.java), [`Invoice.java`](src/main/java/theatricalplays/Invoice.java) — Fixed domain/schema entities.
  * [`StatementPrinter.java`](src/main/java/theatricalplays/StatementPrinter.java) — Original legacy code with tangled state accumulation and misleading comments.
  * [`ModernStatementPrinter.java`](src/main/java/theatricalplays/ModernStatementPrinter.java) — Modernized Java 17+ implementation separating pure calculation (`StatementData`, `LineItem`) from formatting.
  * [`StatementPrinterTests.java`](src/test/java/theatricalplays/StatementPrinterTests.java) — JUnit 5 equivalence and formal boundary vector tests.
* **Quint Formal Verification (`verification/quint/`)**
  * [`theatrical_players.qnt`](verification/quint/theatrical_players.qnt) — State machine model, equivalence invariants, and mutation bug detector.
* **Dafny Formal Verification (`verification/dafny/`)**
  * [`TheatricalPlayers.dfy`](verification/dafny/TheatricalPlayers.dfy) — Full unbounded deductive proof (loop invariants, inductive lemmas, and `ensures` contracts) proving `LegacyStatementPrinter == ModernStatementPrinter` for all valid invoices of any length.

---

## What Formal Verification Uncovered in `StatementPrinter.java`

1. **The Misleading Comment Trap (Caught by Quint & Dafny):**
   * In `StatementPrinter.java` (lines 40–41):
     ```java
     // add extra credit for every ten comedy attendees
     if ("comedy".equals(play.type)) volumeCredits += Math.floor(perf.audience / 5);
     ```
   * An SME, developer, or LLM relying on comments/specs would modernize this to `audience / 10`.
   * Both **Quint** (`buggyCommentEquivalenceInv`) and **Dafny** immediately flag this with a concrete counterexample (e.g., `audience = 5` yields `1` credit in legacy vs `0` in the comment-based rewrite).
2. **The Hidden Integer Division Invariant (`thisAmount / 100`):**
   * In `StatementPrinter.java` (line 44): `frmt.format(thisAmount / 100)` performs `int / int` division before formatting currency.
   * Why didn't legacy lose cents? Both [`theatrical_players.qnt`](verification/quint/theatrical_players.qnt) (`noLostCentsInIntegerDivisionInv`) and [`TheatricalPlayers.dfy`](verification/dafny/TheatricalPlayers.dfy) (`LemmaAmountAlwaysMultipleOf100`) prove that for all valid Tragedy and Comedy performances, `thisAmount % 100 == 0` always holds.

---

## Running the Formal Verification Suites

### 1. Quint (`verification/quint/theatrical_players.qnt`)

Install Quint CLI (if not installed):
```bash
npm install -g @informalsystems/quint
```

Run Quint formal unit & boundary tests:
```bash
quint test verification/quint/theatrical_players.qnt
```

Simulate 10,000 random invoice trajectories and verify 100% equivalence (`fullEquivalenceInv`):
```bash
quint run --invariant=fullEquivalenceInv verification/quint/theatrical_players.qnt
```

Symbolically verify with Z3/Apalache:
```bash
quint verify --invariant=fullEquivalenceInv verification/quint/theatrical_players.qnt
```

Watch Quint catch the misleading comment bug (`audience / 10` vs `audience / 5`) and print a counterexample trace:
```bash
quint run --invariant=buggyCommentEquivalenceInv verification/quint/theatrical_players.qnt
```

---

### 2. Dafny (`verification/dafny/TheatricalPlayers.dfy`)

Install Dafny (via Homebrew on macOS):
```bash
brew install dafny
```

Mathematically prove all lemmas, loop invariants, and `Legacy == Modern` equivalence:
```bash
dafny verify verification/dafny/TheatricalPlayers.dfy
```

Run the verified Dafny test suite:
```bash
dafny test verification/dafny/TheatricalPlayers.dfy
```

Execute the verified Dafny model:
```bash
dafny run verification/dafny/TheatricalPlayers.dfy
```

Compile the Dafny specification directly into a Java `.jar`:
```bash
dafny build --target:java verification/dafny/TheatricalPlayers.dfy
```

---

### 3. Java JUnit 5 Equivalence Suite

Run via Maven (root directory) or Gradle (`java/` directory):
```bash
mvn test
# or using the included Gradle wrapper:
cd java && ./gradlew test
```
