package model;

/**
 * Represents a mark in the Othello game. There three possible values:
 * Mark.XX(Black point), Mark.OO(White point) and Mark.EMPTY.
 * Module 2 lab assignment
 */
public enum Mark {
    EMPTY(" "),XX("\u25A1"), OO("\u25A0");

    private final String symbol;

    Mark(String symbol) {
        this.symbol = symbol;
    }

    /**
     * Return the symbol
     * @return the symbol of mark ( black point, white point, white space)
     */

    public String getSymbol() {
        return symbol;
    }
}