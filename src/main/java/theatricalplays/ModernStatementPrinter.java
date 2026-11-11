package theatricalplays;

import java.text.NumberFormat;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * Modernized implementation of StatementPrinter.
 * Separates domain calculation (StatementData / LineItem) from text rendering,
 * using polymorphic/pure functions verified against Legacy StatementPrinter
 * via Quint and Dafny formal models.
 */
public class ModernStatementPrinter {

    public record LineItem(String playName, int audience, int amount, int volumeCredits) {}

    public record StatementData(
            String customer,
            List<LineItem> lines,
            int totalAmount,
            int totalVolumeCredits
    ) {}

    public String print(Invoice invoice, Map<String, Play> plays) {
        StatementData data = evaluate(invoice, plays);
        return renderPlainText(data);
    }

    public StatementData evaluate(Invoice invoice, Map<String, Play> plays) {
        List<LineItem> lines = invoice.performances.stream()
                .map(perf -> evaluatePerformance(perf, plays.get(perf.playID)))
                .toList();

        int totalAmount = lines.stream().mapToInt(LineItem::amount).sum();
        int totalCredits = lines.stream().mapToInt(LineItem::volumeCredits).sum();

        return new StatementData(invoice.customer, lines, totalAmount, totalCredits);
    }

    public LineItem evaluatePerformance(Performance perf, Play play) {
        int amount = switch (play.type) {
            case "tragedy" -> tragedyAmount(perf.audience);
            case "comedy" -> comedyAmount(perf.audience);
            default -> throw new Error("unknown type: %s".formatted(play.type));
        };

        int credits = switch (play.type) {
            case "tragedy" -> baseCredits(perf.audience);
            case "comedy" -> baseCredits(perf.audience) + comedyExtraCredits(perf.audience);
            default -> throw new Error("unknown type: %s".formatted(play.type));
        };

        return new LineItem(play.name, perf.audience, amount, credits);
    }

    public static int tragedyAmount(int audience) {
        return (audience > 30)
                ? 40000 + 1000 * (audience - 30)
                : 40000;
    }

    public static int comedyAmount(int audience) {
        int base = 30000 + 300 * audience;
        return (audience > 20)
                ? base + 10000 + 500 * (audience - 20)
                : base;
    }

    public static int baseCredits(int audience) {
        return Math.max(audience - 30, 0);
    }

    public static int comedyExtraCredits(int audience) {
        // Verified against legacy code (audience / 5), NOT the misleading legacy comment ("every ten")
        return (int) Math.floor(audience / 5);
    }

    private String renderPlainText(StatementData data) {
        NumberFormat frmt = NumberFormat.getCurrencyInstance(Locale.US);
        StringBuilder result = new StringBuilder();
        result.append(String.format("Statement for %s%n", data.customer()));

        for (LineItem line : data.lines()) {
            result.append(String.format(
                    "  %s: %s (%s seats)%n",
                    line.playName(),
                    frmt.format(line.amount() / 100),
                    line.audience()
            ));
        }

        result.append(String.format("Amount owed is %s%n", frmt.format(data.totalAmount() / 100)));
        result.append(String.format("You earned %s credits%n", data.totalVolumeCredits()));
        return result.toString();
    }
}
