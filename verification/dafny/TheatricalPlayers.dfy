/**
 * Formal Verification Specification & Equivalence Proof for Theatrical Players Refactoring Kata
 * Tool: Dafny (Verification-Aware Programming Language backed by Z3)
 *
 * Commands to run:
 *   1. Mathematically prove all preconditions, loop invariants, lemmas, and equivalence postconditions:
 *      dafny verify verification/dafny/TheatricalPlayers.dfy
 *
 *   2. Run the verified {:test} suite:
 *      dafny test verification/dafny/TheatricalPlayers.dfy
 *
 *   3. Execute the verified model directly:
 *      dafny run verification/dafny/TheatricalPlayers.dfy
 *
 *   4. Compile the verified Dafny specification directly into Java (.jar):
 *      dafny build --target:java verification/dafny/TheatricalPlayers.dfy
 */

module TheatricalPlayersVerification {

  // =========================================================================
  // 1. DOMAIN MODEL & SCHEMA INVARIANTS
  // =========================================================================

  datatype PlayType = Tragedy | Comedy

  datatype Play = Play(name: string, playType: PlayType)

  datatype Performance = Performance(playID: string, audience: int)

  datatype Invoice = Invoice(customer: string, performances: seq<Performance>)

  datatype LineItem = LineItem(playName: string, audience: int, amount: int, volumeCredits: int)

  datatype StatementResult = StatementResult(
    customer: string,
    lines: seq<LineItem>,
    totalAmount: int,
    totalVolumeCredits: int
  )

  // Domain constraint: Audience cannot be negative, and playID must exist in the catalog
  predicate ValidPerformance(perf: Performance, plays: map<string, Play>) {
    perf.playID in plays && perf.audience >= 0
  }

  predicate ValidInvoice(invoice: Invoice, plays: map<string, Play>) {
    forall i :: 0 <= i < |invoice.performances| ==> ValidPerformance(invoice.performances[i], plays)
  }

  function Max(a: int, b: int): int {
    if a > b then a else b
  }

  // =========================================================================
  // 2. LEGACY SPECIFICATION (Direct Translation of StatementPrinter.java)
  // =========================================================================

  function LegacyPerfAmount(perf: Performance, play: Play): int
    requires perf.audience >= 0
  {
    match play.playType
    case Tragedy =>
      var thisAmount := 40000;
      if perf.audience > 30 then
        thisAmount + 1000 * (perf.audience - 30)
      else
        thisAmount
    case Comedy =>
      var thisAmount := 30000;
      var withSurcharge :=
        if perf.audience > 20 then
          thisAmount + 10000 + 500 * (perf.audience - 20)
        else
          thisAmount;
      withSurcharge + 300 * perf.audience
  }

  function LegacyPerfCredits(perf: Performance, play: Play): int
    requires perf.audience >= 0
  {
    var volumeCredits := Max(perf.audience - 30, 0);
    // Legacy Java code: if ("comedy".equals(play.type)) volumeCredits += Math.floor(perf.audience / 5);
    if play.playType == Comedy then
      volumeCredits + (perf.audience / 5)
    else
      volumeCredits
  }

  function LegacyLineSpec(perf: Performance, play: Play): LineItem
    requires perf.audience >= 0
  {
    LineItem(
      play.name,
      perf.audience,
      LegacyPerfAmount(perf, play),
      LegacyPerfCredits(perf, play)
    )
  }

  function LegacyLinesSpec(perfs: seq<Performance>, plays: map<string, Play>): seq<LineItem>
    requires forall i :: 0 <= i < |perfs| ==> ValidPerformance(perfs[i], plays)
  {
    if |perfs| == 0 then []
    else
      var init := perfs[..|perfs|-1];
      var last := perfs[|perfs|-1];
      LegacyLinesSpec(init, plays) + [LegacyLineSpec(last, plays[last.playID])]
  }

  function LegacyTotalAmountSpec(perfs: seq<Performance>, plays: map<string, Play>): int
    requires forall i :: 0 <= i < |perfs| ==> ValidPerformance(perfs[i], plays)
  {
    if |perfs| == 0 then 0
    else
      var init := perfs[..|perfs|-1];
      var last := perfs[|perfs|-1];
      LegacyTotalAmountSpec(init, plays) + LegacyPerfAmount(last, plays[last.playID])
  }

  function LegacyTotalCreditsSpec(perfs: seq<Performance>, plays: map<string, Play>): int
    requires forall i :: 0 <= i < |perfs| ==> ValidPerformance(perfs[i], plays)
  {
    if |perfs| == 0 then 0
    else
      var init := perfs[..|perfs|-1];
      var last := perfs[|perfs|-1];
      LegacyTotalCreditsSpec(init, plays) + LegacyPerfCredits(last, plays[last.playID])
  }

  // =========================================================================
  // 3. MODERNIZED SPECIFICATION (Direct Translation of ModernStatementPrinter.java)
  // =========================================================================

  function ModernTragedyAmount(audience: int): int
    requires audience >= 0
  {
    if audience > 30 then 40000 + 1000 * (audience - 30) else 40000
  }

  function ModernComedyAmount(audience: int): int
    requires audience >= 0
  {
    var base := 30000 + 300 * audience;
    if audience > 20 then base + 10000 + 500 * (audience - 20) else base
  }

  function ModernBaseCredits(audience: int): int
    requires audience >= 0
  {
    Max(audience - 30, 0)
  }

  function ModernComedyExtraCredits(audience: int): int
    requires audience >= 0
  {
    audience / 5
  }

  function ModernEvaluatePerformance(perf: Performance, play: Play): LineItem
    requires perf.audience >= 0
  {
    var amount := match play.playType
      case Tragedy => ModernTragedyAmount(perf.audience)
      case Comedy  => ModernComedyAmount(perf.audience);

    var credits := match play.playType
      case Tragedy => ModernBaseCredits(perf.audience)
      case Comedy  => ModernBaseCredits(perf.audience) + ModernComedyExtraCredits(perf.audience);

    LineItem(play.name, perf.audience, amount, credits)
  }

  // =========================================================================
  // 4. FORMAL THEOREMS & EQUIVALENCE LEMMAS (Proven Automatically by Z3)
  // =========================================================================

  /**
   * THEOREM 1: Single-Performance Equivalence
   * Proves that for ANY valid performance and play, the refactored Modern functions
   * compute the exact same amount and volume credits as the Legacy switch statement.
   */
  lemma LemmaSinglePerformanceEquivalence(perf: Performance, play: Play)
    requires perf.audience >= 0
    ensures ModernEvaluatePerformance(perf, play) == LegacyLineSpec(perf, play)
    ensures ModernEvaluatePerformance(perf, play).amount == LegacyPerfAmount(perf, play)
    ensures ModernEvaluatePerformance(perf, play).volumeCredits == LegacyPerfCredits(perf, play)
  {
    // Z3 proves all branches (audience <= 20, 21..30, > 30, Tragedy vs Comedy) automatically!
  }

  /**
   * THEOREM 2: Hidden Legacy Property — No Lost Cents in Integer Division
   * In Legacy StatementPrinter.java: `frmt.format(thisAmount / 100)` uses integer division.
   * This theorem proves that for all possible non-negative audiences, `thisAmount`
   * is ALWAYS an exact multiple of 100, so `thisAmount / 100` never truncates cents!
   */
  lemma LemmaAmountAlwaysMultipleOf100(perf: Performance, play: Play)
    requires perf.audience >= 0
    ensures LegacyPerfAmount(perf, play) % 100 == 0
    ensures ModernEvaluatePerformance(perf, play).amount % 100 == 0
  {
    // Proven automatically by Z3 linear integer arithmetic!
  }

  /**
   * THEOREM 3: Domain Non-Negativity Invariant
   * Proves that amounts are always >= 30,000 ($300.00) and credits are always >= 0.
   */
  lemma LemmaDomainBounds(perf: Performance, play: Play)
    requires perf.audience >= 0
    ensures ModernEvaluatePerformance(perf, play).amount >= 30000
    ensures ModernEvaluatePerformance(perf, play).volumeCredits >= 0
  {
  }

  // =========================================================================
  // 5. IMPERATIVE LEGACY METHOD VS. MODERNIZED METHOD EQUIVALENCE
  // =========================================================================

  /**
   * Imperative Legacy Implementation mirroring `StatementPrinter.java`'s single loop
   * mutating `totalAmount` and `volumeCredits` in place.
   */
  method LegacyStatementPrinter(invoice: Invoice, plays: map<string, Play>)
    returns (res: StatementResult)
    requires ValidInvoice(invoice, plays)
    ensures res.customer == invoice.customer
    ensures res.lines == LegacyLinesSpec(invoice.performances, plays)
    ensures res.totalAmount == LegacyTotalAmountSpec(invoice.performances, plays)
    ensures res.totalVolumeCredits == LegacyTotalCreditsSpec(invoice.performances, plays)
  {
    var totalAmount := 0;
    var volumeCredits := 0;
    var lines: seq<LineItem> := [];
    var i := 0;

    while i < |invoice.performances|
      invariant 0 <= i <= |invoice.performances|
      invariant lines == LegacyLinesSpec(invoice.performances[..i], plays)
      invariant totalAmount == LegacyTotalAmountSpec(invoice.performances[..i], plays)
      invariant volumeCredits == LegacyTotalCreditsSpec(invoice.performances[..i], plays)
    {
      var perf := invoice.performances[i];
      var play := plays[perf.playID];
      var thisAmount := 0;

      match play.playType {
        case Tragedy =>
          thisAmount := 40000;
          if perf.audience > 30 {
            thisAmount := thisAmount + 1000 * (perf.audience - 30);
          }
        case Comedy =>
          thisAmount := 30000;
          if perf.audience > 20 {
            thisAmount := thisAmount + 10000 + 500 * (perf.audience - 20);
          }
          thisAmount := thisAmount + 300 * perf.audience;
      }

      var perfCredits := Max(perf.audience - 30, 0);
      if play.playType == Comedy {
        perfCredits := perfCredits + (perf.audience / 5);
      }

      assert invoice.performances[..i+1][..i] == invoice.performances[..i];

      lines := lines + [LineItem(play.name, perf.audience, thisAmount, perfCredits)];
      totalAmount := totalAmount + thisAmount;
      volumeCredits := volumeCredits + perfCredits;
      i := i + 1;
    }

    assert invoice.performances[..|invoice.performances|] == invoice.performances;
    res := StatementResult(invoice.customer, lines, totalAmount, volumeCredits);
  }

  /**
   * Modernized Implementation mirroring `ModernStatementPrinter.java`'s decoupled pipeline:
   * Step 1: Map performances to structured LineItems using pure calculators.
   * Step 2: Sum totalAmount and totalVolumeCredits from the evaluated LineItems.
   *
   * Notice the `ensures` contract: Dafny mathematically proves that this modernized
   * multi-pass implementation produces the EXACT same output as LegacyStatementPrinter!
   */
  method ModernStatementPrinter(invoice: Invoice, plays: map<string, Play>)
    returns (res: StatementResult)
    requires ValidInvoice(invoice, plays)
    ensures res.customer == invoice.customer
    ensures res.lines == LegacyLinesSpec(invoice.performances, plays)
    ensures res.totalAmount == LegacyTotalAmountSpec(invoice.performances, plays)
    ensures res.totalVolumeCredits == LegacyTotalCreditsSpec(invoice.performances, plays)
  {
    // Pass 1: Map each Performance to a LineItem via ModernEvaluatePerformance
    var lines: seq<LineItem> := [];
    var i := 0;
    while i < |invoice.performances|
      invariant 0 <= i <= |invoice.performances|
      invariant |lines| == i
      invariant lines == LegacyLinesSpec(invoice.performances[..i], plays)
    {
      var perf := invoice.performances[i];
      var play := plays[perf.playID];
      LemmaSinglePerformanceEquivalence(perf, play);
      assert invoice.performances[..i+1][..i] == invoice.performances[..i];
      var item := ModernEvaluatePerformance(perf, play);
      lines := lines + [item];
      i := i + 1;
    }
    assert invoice.performances[..|invoice.performances|] == invoice.performances;

    // Pass 2: Sum amounts and credits across the evaluated LineItems
    var totalAmount := 0;
    var totalCredits := 0;
    var j := 0;
    while j < |lines|
      invariant 0 <= j <= |lines|
      invariant totalAmount == LegacyTotalAmountSpec(invoice.performances[..j], plays)
      invariant totalCredits == LegacyTotalCreditsSpec(invoice.performances[..j], plays)
    {
      assert invoice.performances[..j+1][..j] == invoice.performances[..j];
      assert lines[j] == LegacyLineSpec(invoice.performances[j], plays[invoice.performances[j].playID]);
      totalAmount := totalAmount + lines[j].amount;
      totalCredits := totalCredits + lines[j].volumeCredits;
      j := j + 1;
    }

    res := StatementResult(invoice.customer, lines, totalAmount, totalCredits);
  }

  /**
   * TOP-LEVEL EQUIVALENCE HARNESS:
   * Calls both LegacyStatementPrinter and ModernStatementPrinter on ANY arbitrary valid
   * Invoice and Play catalog, and proves at compile-time that `legacyResult == modernResult`.
   */
  method VerifyEndToEndEquivalence(invoice: Invoice, plays: map<string, Play>)
    requires ValidInvoice(invoice, plays)
  {
    var legacyResult := LegacyStatementPrinter(invoice, plays);
    var modernResult := ModernStatementPrinter(invoice, plays);
    assert legacyResult == modernResult;
  }

  // =========================================================================
  // 6. EXECUTABLE VERIFIED TESTS & MAIN ENTRYPOINT
  // =========================================================================

  method {:test} TestGoldenMasterInvoice() {
    var plays := map[
      "hamlet" := Play("Hamlet", Tragedy),
      "as-like" := Play("As You Like It", Comedy),
      "othello" := Play("Othello", Tragedy)
    ];

    var invoice := Invoice("BigCo", [
      Performance("hamlet", 55),
      Performance("as-like", 35),
      Performance("othello", 40)
    ]);

    var legacyRes := LegacyStatementPrinter(invoice, plays);
    var modernRes := ModernStatementPrinter(invoice, plays);

    expect legacyRes == modernRes, "Modern result must equal Legacy result";
    expect modernRes.totalAmount == 173000, "Total amount must be 173000 cents ($1,730.00)";
    expect modernRes.totalVolumeCredits == 47, "Total volume credits must be 47";
  }

  method Main() {
    var plays := map[
      "hamlet" := Play("Hamlet", Tragedy),
      "as-like" := Play("As You Like It", Comedy),
      "othello" := Play("Othello", Tragedy)
    ];

    var invoice := Invoice("BigCo", [
      Performance("hamlet", 55),
      Performance("as-like", 35),
      Performance("othello", 40)
    ]);

    var legacyRes := LegacyStatementPrinter(invoice, plays);
    var modernRes := ModernStatementPrinter(invoice, plays);

    print "=== Dafny Formal Verification POC: Theatrical Players ===\n";
    print "Customer: ", modernRes.customer, "\n";
    print "Legacy Total (cents): ", legacyRes.totalAmount, " | Modern Total (cents): ", modernRes.totalAmount, "\n";
    print "Legacy Credits:       ", legacyRes.totalVolumeCredits, " | Modern Credits:       ", modernRes.totalVolumeCredits, "\n";
    print "Mathematically Equivalent: ", legacyRes == modernRes, "\n";
  }
}
