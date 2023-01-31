package model.Move;

import model.Move.Move;

public class OthelloMove implements Move {
    private final int row;
    private final int col;
    private final String m;

    /**
     * Creates an instance of a TicTacToe move with given mark, row and column
     * @param m mark of new move
     * @param row row of new move
     * @param col colume of new move;
     */
    public OthelloMove(String m, int row, int col) {
        this.m = m;
        this.row = row;
        this.col = col;
    }
    /**
     * Returns the mark of this move
     * @return this move's mark
     */
    //@ pure;
    @Override
    public String getMark() {
        return this.m;
    }

    /**
     * Returns the row of this particular move
     * @return row of this move
     */
    //@ pure;
    @Override
    public int getRow() {
        return this.row;
    }

    /**
     * Returns the column of this particular move
     * @return column of this move
     */
    //@ pure;
    @Override
    public int getCol() {
        return this.col;
    }

}
