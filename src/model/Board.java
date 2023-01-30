package model;

public class Board {

    /**
     * 2- Dimension of the board, i.e., if set to 8, the board has 8 rows and 8 columns.
     */
    public static final int DIM = 8;
    private static final String[] NUMBERING = {
            "0,0|0,1|0,2|0,3|0,4|0,5|0,6|0,7",
            "---+---+---+---+---+---+---+---+",
            "1,0|1,1|1,2|1,3|1,4|1,5|1,6|1,7",
            "---+---+---+---+---+---+---+---+",
            "2,0|2,1|2,2|2,3|2,4|2,5|2,6|2,7",
            "---+---+---+---+---+---+---+---+",
            "3,0|3,1|3,2|3,3|3,4|3,5|3,6|3,7",
            "---+---+---+---+---+---+---+---+",
            "4,0|4,1|4,2|4,3|4,4|4,5|4,6|4,7",
            "---+---+---+---+---+---+---+---+",
            "5,0|5,1|5,2|5,3|5,4|5,5|5,6|5,7",
            "---+---+---+---+---+---+---+---+",
            "6,0|6,1|6,2|6,3|6,4|6,5|6,6|6,7",
            "---+---+---+---+---+---+---+---+",
            "7,0|7,1|7,2|7,3|7,4|7,5|7,6|7,7",
            "---+---+---+---+---+---+---+---+",};

    private static final String LINE = NUMBERING[1];

    /**
     * The DIM by DIM fields of the Othello board. See NUMBERING for the
     * coding of the fields.
     */
    private final String[][] fields;

    // -- Constructors -----------------------------------------------

    /**
     * Creates an initial board.
     */
    public Board() {
        fields = new String[DIM][DIM];
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                this.fields[i][j] = Mark.EMPTY.getSymbol();
            }
        }
        fields[3][3] = Mark.OO.getSymbol();
        fields[3][4] = Mark.XX.getSymbol();
        fields[4][3] = Mark.XX.getSymbol();
        fields[4][4] = Mark.OO.getSymbol();
    }

    /**
     * Creates a deep copy of this field.
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < DIM*DIM); \result.fields[i] == this.fields[i]);
     @*/
    public Board deepCopy() {
        Board copy = new Board();
        for (int i = 0; i < fields.length; i++) {
            System.arraycopy(fields[i], 0, copy.fields[i], 0, fields[i].length);
        }
        return copy;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     *
     * @return  the (row,col)-field
     */
    //@ ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
    public boolean isField(int row, int col) {
        return DIM > row && row >= 0 && DIM > col && col >= 0;
    }


    /**
     * Returns the content of the field i.
     *
     * @param (row, col) the number of the field (see NUMBERING)
     * @return the mark on the field
     */
    /*@ requires isField(row, col);
    ensures \result == Mark.EMPTY.getSymbol() || \result == Mark.OO.getSymbol() || \result == Mark.XX.getSymbol();
     @*/
    public String getField(int row, int col) {
        return fields[row][col];
    }


    /**
     * Returns true if the field[row][col] is empty.
     *
     * @param (row ,col) the index of the field
     * @return true if the field is empty
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == Mark.EMPTY.getSymbol() ==> \result == true;
     @*/
    public boolean isEmptyField(int row, int col) {
        return fields[row][col].equals(Mark.EMPTY.getSymbol());
    }


    /**
     * Sets the content of the field represented by
     * the (row,col) pair to the mark m.
     *
     * @param row the field's row
     * @param col the field's column
     * @param m   the mark to be placed
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == m;
     @*/
    public void setField(int row, int col, String m) {
        fields[row][col] = m;
    }


    /**
     * Tests if the whole board is full.
     *
     * @return true if all fields are occupied
     */

    //@ ensures (\forall int i; 0 <= i && i < DIM;(\forall int j; 0 <= j && j < DIM; fields[i][j] != Mark.EMPTY.getSymbol()) ==> \result)&& (\exists int i; 0 <= i && i < DIM;(\exists int j; 0 <= j && j < DIM; fields[i][j] == Mark.EMPTY.getSymbol()) ==> !\result);
    public boolean isFull() {
        for (int i = 0 ; i < DIM; i ++) {
            for (int j = 0 ; j < DIM ; j ++) {
                if (fields[i][j].equals(Mark.EMPTY.getSymbol())) {
                    return false;
                }
            }
        }
        return true;
    }


    /**
     * Empties all fields of this board .
     */
    //@ ensures (\forall int i; 0 <= i && i < DIM;(\forall int j; 0 <= j && j < DIM; fields[i][j] == Mark.EMPTY.getSymbol()));

    public void reset() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                fields[i][j] = Mark.EMPTY.getSymbol();
            }
        }
        fields[3][3] = Mark.OO.getSymbol();
        fields[3][4] = Mark.XX.getSymbol();
        fields[4][3] = Mark.XX.getSymbol();
        fields[4][4] = Mark.OO.getSymbol();

    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public  String toString() {
        String s = "   A   B   C   D   E   F   G   H \n";
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                row += " " + getField(i, j).substring(0, 1).replace("E", " ") + " ";
                if (j < DIM - 1) {
                    if(j == 0){
                        row =  i+ " " + row + "|";
                    }else {
                        row = row + "|";
                    }
                }
            }
            s = s + row;
            if (i < DIM - 1) {
                s = s + "\n" + "  "+ LINE + "\n";
            }
        }
        return s;
    }
    public static void main (String[] arg){
        Board board = new Board();
        Board board1 = board.deepCopy();
        board1.setField(1,1,Mark.OO.getSymbol());
        System.out.println(board);
        System.out.println(board1);

    }
}