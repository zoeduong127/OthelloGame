package model.Move;

/**
 * A move in a turn-based game.
 */
public interface Move {
    /**
     * Get the number row of move
     * @return the row of move
     */
    //@ pure;
    int getRow();

    /**
     * Get the number colume of move
     * @return colume of move
     */
    //@ pure;
    int getCol();

    /**
     * Get the mark of this move
     * @return mark of move
     */
    //@ pure;
    String getMark();

}
