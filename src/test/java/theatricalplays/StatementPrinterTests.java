package theatricalplays;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public class StatementPrinterTests {

    private static final Map<String, Play> SAMPLE_PLAYS = Map.of(
            "hamlet", new Play("Hamlet", "tragedy"),
            "as-like", new Play("As You Like It", "comedy"),
            "othello", new Play("Othello", "tragedy")
    );

    @Test
    void exampleStatementMatchesGoldenOutput() {
        Invoice invoice = new Invoice("BigCo", List.of(
                new Performance("hamlet", 55),
                new Performance("as-like", 35),
                new Performance("othello", 40)
        ));

        StatementPrinter legacyPrinter = new StatementPrinter();
        ModernStatementPrinter modernPrinter = new ModernStatementPrinter();

        String expected = """
                Statement for BigCo
                  Hamlet: $650.00 (55 seats)
                  As You Like It: $580.00 (35 seats)
                  Othello: $500.00 (40 seats)
                Amount owed is $1,730.00
                You earned 47 credits
                """;

        assertEquals(expected, legacyPrinter.print(invoice, SAMPLE_PLAYS));
        assertEquals(expected, modernPrinter.print(invoice, SAMPLE_PLAYS));
    }

    @Test
    void statementWithNewPlayTypesThrowsIdenticalError() {
        Map<String, Play> plays = Map.of(
                "henry-v", new Play("Henry V", "history"),
                "as-like", new Play("As You Like It", "pastoral")
        );

        Invoice invoice = new Invoice("BigCo", List.of(
                new Performance("henry-v", 53),
                new Performance("as-like", 55)
        ));

        StatementPrinter legacyPrinter = new StatementPrinter();
        ModernStatementPrinter modernPrinter = new ModernStatementPrinter();

        Error legacyErr = assertThrows(Error.class, () -> legacyPrinter.print(invoice, plays));
        Error modernErr = assertThrows(Error.class, () -> modernPrinter.print(invoice, plays));
        assertEquals(legacyErr.getMessage(), modernErr.getMessage());
    }

    /**
     * Boundary Equivalence Test Suite generated from the Quint & Dafny formal models:
     * Covers exact threshold boundaries:
     * - audience = 0, 1, 4, 5 (comedy credit floor step boundary)
     * - audience = 19, 20, 21 (comedy surcharge threshold > 20)
     * - audience = 29, 30, 31 (tragedy surcharge & base volume credit threshold > 30)
     * - audience = 100 (large audience)
     */
    @Test
    void formalBoundaryVectorsEquivalence() {
        int[] boundaryAudiences = {0, 1, 4, 5, 6, 9, 10, 19, 20, 21, 29, 30, 31, 35, 40, 55, 100};

        StatementPrinter legacyPrinter = new StatementPrinter();
        ModernStatementPrinter modernPrinter = new ModernStatementPrinter();

        for (int a1 : boundaryAudiences) {
            for (int a2 : boundaryAudiences) {
                Invoice invoice = new Invoice("FormalVerifierCustomer", List.of(
                        new Performance("hamlet", a1),
                        new Performance("as-like", a2)
                ));
                assertEquals(
                        legacyPrinter.print(invoice, SAMPLE_PLAYS),
                        modernPrinter.print(invoice, SAMPLE_PLAYS),
                        "Divergence at tragedy=" + a1 + ", comedy=" + a2
                );
            }
        }
    }
}
