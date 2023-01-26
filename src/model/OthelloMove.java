package model;

public class OthelloMove implements Move{
    private int row;
    private int col;
    private String m;

    /**
     * Creates an instance of a TicTacToe move with given mark, row and column
     * @param m
     * @param row
     * @param col
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
    public String getMark() {
        return this.m;
    }

    /**
     * Returns the row of this particular move
     * @return row of this move
     */
    public int getRow() {
        return this.row;
    }

    /**
     * Returns the column of this particular move
     * @return column of this move
     */
    public int getCol() {
        return this.col;
    }

}
