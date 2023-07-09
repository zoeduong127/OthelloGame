package model.Move;

/**
 * Represents a mark in the Othello game. There three possible values:
 * Mark.XX(Black point), Mark.OO(Red point) and Mark.EMPTY(space).
 * Module 2 lab assignment
 */
public enum Mark {
    EMPTY(" "),XX("\u001b[30m\u25CF"), OO("\u001b[31m\u25CF");
    private final String symbol;

    Mark(String symbol) {
        this.symbol = symbol;
    }

    /**
     * Return the symbol
     * @return the symbol of mark ( black point, white point, white space)
     */
    //@ pure;
    public String getSymbol() {
        return symbol;
    }



}