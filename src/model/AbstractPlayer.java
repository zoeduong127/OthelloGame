package model;


/**
 * A player of a game.
 */
public abstract class AbstractPlayer implements Player {
    private final String name;

    /**
     * Creates a new Player object.
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    public String getName() {
        return name;
    }

    /**
     * Determines the next move, if the game still has available moves.
     * @param game the current game
     * @return the player's choice
     */
    //@ requires !game.isGameOver();
//    @ ensures game.isValidMove(\result);
    public abstract OthelloMove determineMove(OthelloGame game);

    /**
     * Returns a representation of a player, i.e., their name
     * @return the String representation of this object
     */
    @Override
    public String toString() {
        return "Player " + name;
    }
}