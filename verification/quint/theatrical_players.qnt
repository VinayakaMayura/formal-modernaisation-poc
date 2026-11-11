// -*- mode: quint; -*-
/**
 * Formal Verification Specification for Theatrical Players Refactoring Kata
 * Tool: Quint (State Machine Simulator & Apalache/Z3 Symbolic Model Checker)
 *
 * Commands to run:
 *   1. Run built-in formal unit & boundary tests:
 *      quint test verification/quint/theatrical_players.qnt
 *
 *   2. Simulate 10,000+ stateful invoice transitions & check equivalence invariants:
 *      quint run --invariant=fullEquivalenceInv verification/quint/theatrical_players.qnt
 *
 *   3. Prove equivalence symbolically with Z3 (via Apalache):
 *      quint verify --invariant=fullEquivalenceInv verification/quint/theatrical_players.qnt
 *
 *   4. Demonstrate bug detection (catching the misleading legacy comment `audience / 10` vs `audience / 5`):
 *      quint run --invariant=buggyCommentEquivalenceInv verification/quint/theatrical_players.qnt
 */
module theatrical_players {

  // =========================================================================
  // 1. DOMAIN TYPES (Mirroring Java Entities & Fixed Schema)
  // =========================================================================

  type Play = {
    name: str,
    playType: str
  }

  type Performance = {
    playID: str,
    audience: int
  }

  type LineItem = {
    playName: str,
    audience: int,
    amount: int,
    credits: int
  }

  type StatementSummary = {
    totalAmount: int,
    volumeCredits: int,
    lines: List[LineItem]
  }

  pure def max(a: int, b: int): int = {
    if (a > b) a else b
  }

  // Domain Precondition: Valid Performance in DB/Input
  pure def validPerformance(perf: Performance, plays: str -> Play): bool = {
    plays.keys().contains(perf.playID) and perf.audience >= 0 and perf.audience <= 500
  }

  // =========================================================================
  // 2. LEGACY IMPLEMENTATION MODEL (Translated 1-to-1 from StatementPrinter.java)
  // =========================================================================

  /**
   * Mirrors a single iteration of the legacy `for (Performance perf : invoice.performances)`
   * loop in `StatementPrinter.java`, mutating `totalAmount`, `volumeCredits`, and `lines`.
   */
  pure def legacyLoopStep(acc: StatementSummary, perf: Performance, plays: str -> Play): StatementSummary = {
    val play = plays.get(perf.playID)

    // switch (play.type) in Legacy Java
    val thisAmount =
      if (play.playType == "tragedy") {
        val base = 40000
        if (perf.audience > 30) base + 1000 * (perf.audience - 30) else base
      } else if (play.playType == "comedy") {
        val base = 30000
        val withSurcharge = if (perf.audience > 20) base + 10000 + 500 * (perf.audience - 20) else base
        withSurcharge + 300 * perf.audience
      } else {
        -1 // Error state for unknown play type
      }

    // Legacy volume credits accumulation
    val stepCredits1 = max(perf.audience - 30, 0)
    // Legacy quirk: comment says "every ten comedy attendees", code does `perf.audience / 5`
    val stepCredits2 = if (play.playType == "comedy") stepCredits1 + (perf.audience / 5) else stepCredits1

    val line: LineItem = {
      playName: play.name,
      audience: perf.audience,
      amount: thisAmount,
      credits: stepCredits2
    }

    {
      totalAmount: acc.totalAmount + thisAmount,
      volumeCredits: acc.volumeCredits + stepCredits2,
      lines: acc.lines.append(line)
    }
  }

  pure def evaluateLegacy(performances: List[Performance], plays: str -> Play): StatementSummary = {
    val empty: StatementSummary = { totalAmount: 0, volumeCredits: 0, lines: List() }
    performances.foldl(empty, (acc, perf) => legacyLoopStep(acc, perf, plays))
  }

  // =========================================================================
  // 3. MODERNIZED IMPLEMENTATION MODEL (Translated from ModernStatementPrinter.java)
  // =========================================================================

  pure def modernTragedyAmount(audience: int): int = {
    if (audience > 30) 40000 + 1000 * (audience - 30) else 40000
  }

  pure def modernComedyAmount(audience: int): int = {
    val base = 30000 + 300 * audience
    if (audience > 20) base + 10000 + 500 * (audience - 20) else base
  }

  pure def modernBaseCredits(audience: int): int = {
    max(audience - 30, 0)
  }

  pure def modernComedyExtraCredits(audience: int): int = {
    audience / 5
  }

  pure def modernEvaluatePerformance(perf: Performance, play: Play): LineItem = {
    val amount =
      if (play.playType == "tragedy") modernTragedyAmount(perf.audience)
      else if (play.playType == "comedy") modernComedyAmount(perf.audience)
      else -1

    val credits =
      if (play.playType == "tragedy") modernBaseCredits(perf.audience)
      else if (play.playType == "comedy") modernBaseCredits(perf.audience) + modernComedyExtraCredits(perf.audience)
      else 0

    {
      playName: play.name,
      audience: perf.audience,
      amount: amount,
      credits: credits
    }
  }

  /**
   * Modernized evaluation separates line mapping, totalAmount reduction, and volumeCredits reduction
   * (mirroring Java Streams in ModernStatementPrinter.java).
   */
  pure def evaluateModern(performances: List[Performance], plays: str -> Play): StatementSummary = {
    val lines = performances.foldl(List(), (acc, perf) =>
      acc.append(modernEvaluatePerformance(perf, plays.get(perf.playID)))
    )
    val totalAmount = lines.foldl(0, (sum, line) => sum + line.amount)
    val volumeCredits = lines.foldl(0, (sum, line) => sum + line.credits)

    {
      totalAmount: totalAmount,
      volumeCredits: volumeCredits,
      lines: lines
    }
  }

  // =========================================================================
  // 4. MUTATION / BUG MODEL: What if a developer trusted the Legacy Comment?
  // =========================================================================
  // In StatementPrinter.java:
  //   // add extra credit for every ten comedy attendees
  //   if ("comedy".equals(play.type)) volumeCredits += Math.floor(perf.audience / 5);
  // If an SME/developer/LLM modernizes this using the comment (`audience / 10`),
  // Quint will immediately catch the divergence and output a counterexample trace!
  pure def evaluateBuggyCommentModern(performances: List[Performance], plays: str -> Play): StatementSummary = {
    val lines = performances.foldl(List(), (acc, perf) => {
      val play = plays.get(perf.playID)
      val cleanLine = modernEvaluatePerformance(perf, play)
      val buggyCredits =
        if (play.playType == "comedy") modernBaseCredits(perf.audience) + (perf.audience / 10)
        else modernBaseCredits(perf.audience)
      acc.append({ ...cleanLine, credits: buggyCredits })
    })
    val totalAmount = lines.foldl(0, (sum, line) => sum + line.amount)
    val volumeCredits = lines.foldl(0, (sum, line) => sum + line.credits)
    { totalAmount: totalAmount, volumeCredits: volumeCredits, lines: lines }
  }

  // =========================================================================
  // 5. STATE MACHINE FOR SIMULATION & SYMBOLIC MODEL CHECKING
  // =========================================================================

  pure val CATALOG: str -> Play = Map(
    "hamlet" -> { name: "Hamlet", playType: "tragedy" },
    "as-like" -> { name: "As You Like It", playType: "comedy" },
    "othello" -> { name: "Othello", playType: "tragedy" }
  )

  var invoicePerformances: List[Performance]
  var legacyOut: StatementSummary
  var modernOut: StatementSummary
  var buggyModernOut: StatementSummary

  action init = all {
    invoicePerformances' = List(),
    legacyOut' = evaluateLegacy(List(), CATALOG),
    modernOut' = evaluateModern(List(), CATALOG),
    buggyModernOut' = evaluateBuggyCommentModern(List(), CATALOG)
  }

  // Action: Add any valid performance with audience in [0..100] (including all threshold boundaries)
  action addPerformance(playID: str, audience: int): bool = all {
    CATALOG.keys().contains(playID),
    audience >= 0,
    audience <= 100,
    val nextPerfs = invoicePerformances.append({ playID: playID, audience: audience })
    all {
      invoicePerformances' = nextPerfs,
      legacyOut' = evaluateLegacy(nextPerfs, CATALOG),
      modernOut' = evaluateModern(nextPerfs, CATALOG),
      buggyModernOut' = evaluateBuggyCommentModern(nextPerfs, CATALOG)
    }
  }

  action step = {
    nondet playID = oneOf(Set("hamlet", "as-like", "othello"))
    nondet audience = oneOf(0.to(100))
    addPerformance(playID, audience)
  }

  // =========================================================================
  // 6. FORMAL INVARIANTS (Verified by `quint run` and `quint verify`)
  // =========================================================================

  // Invariant 1: 100% Behavioral Equivalence between Legacy and Modernized code
  val fullEquivalenceInv: bool = and {
    legacyOut.totalAmount == modernOut.totalAmount,
    legacyOut.volumeCredits == modernOut.volumeCredits,
    legacyOut.lines == modernOut.lines
  }

  // Invariant 2: Hidden Legacy Property — Amounts in cents are ALWAYS multiples of 100
  // (Explains why `thisAmount / 100` integer division in Java never truncated cents!)
  val noLostCentsInIntegerDivisionInv: bool = and {
    legacyOut.totalAmount % 100 == 0,
    modernOut.totalAmount % 100 == 0
  }

  // Invariant 3: Domain Safety — Amounts and credits are never negative for valid audiences
  val domainSafetyInv: bool = and {
    modernOut.totalAmount >= 0,
    modernOut.volumeCredits >= 0
  }

  // Invariant 4: Expected to FAIL when checked! Demonstrates how Quint catches the `/ 10` comment bug
  val buggyCommentEquivalenceInv: bool = {
    legacyOut.volumeCredits == buggyModernOut.volumeCredits
  }

  // =========================================================================
  // 7. EXECUTABLE FORMAL TEST SUITE (`quint test`)
  // =========================================================================

  // Test 1: Martin Fowler's Golden Master Invoice (Hamlet 55, As You Like It 35, Othello 40)
  run goldenMasterInvoiceTest = {
    init
      .then(addPerformance("hamlet", 55))
      .then(addPerformance("as-like", 35))
      .then(addPerformance("othello", 40))
      .then(all {
        assert(legacyOut.totalAmount == 173000), // $1,730.00
        assert(legacyOut.volumeCredits == 47),   // 25 + (5 + 7) + 10 = 47 credits
        assert(fullEquivalenceInv),
        assert(noLostCentsInIntegerDivisionInv),
        invoicePerformances' = invoicePerformances,
        legacyOut' = legacyOut,
        modernOut' = modernOut,
        buggyModernOut' = buggyModernOut
      })
  }

  // Test 2: Exact Threshold Boundaries (0, 19, 20, 21 for Comedy; 29, 30, 31 for Tragedy)
  run thresholdBoundariesTest = {
    init
      .then(addPerformance("as-like", 0))
      .then(addPerformance("as-like", 19))
      .then(addPerformance("as-like", 20))
      .then(addPerformance("as-like", 21))
      .then(addPerformance("hamlet", 29))
      .then(addPerformance("hamlet", 30))
      .then(addPerformance("hamlet", 31))
      .then(all {
        assert(fullEquivalenceInv),
        assert(noLostCentsInIntegerDivisionInv),
        invoicePerformances' = invoicePerformances,
        legacyOut' = legacyOut,
        modernOut' = modernOut,
        buggyModernOut' = buggyModernOut
      })
  }
}
