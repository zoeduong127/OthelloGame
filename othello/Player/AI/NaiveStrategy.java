package Player.AI;

import model.MainGame.Game;
import model.Move.Move;
import model.Move.OthelloMove;

import java.util.List;
import java.util.Random;
/**
 * Implements the Strategy interface to define a Naive Strategy.
 */
public class NaiveStrategy implements Strategy {
    private final String name;
   // Constructor for default bot
    public NaiveStrategy() {
        this.name = "Naive Strategy";
    }
    // Constructor for a bot with a given name;
    public NaiveStrategy(String name){this.name = name;}

    /**
     * Getter for the name of the Strategy.
     * @return String name of the Strategy
     */
    //@ ensures \result instanceof String;
    //@ pure;
    @Override
    public String getName() {
        return name;
    }

    /**
     * Determines the move to be played by the Naive Strategy.
     * @param game The instance of Otheloo that is being played
     * @return Move selected randomly from the currently available moves.
     */
    //@ requires game != null;
    //@ ensures \result instanceof Move;
    @Override
    public Move determineMove(Game game) {
        List<Move> validMoves = game.getValidMoves();
        if(validMoves.size() > 0) {
            Random rand = new Random();
            int value = rand.nextInt(game.getValidMoves().size());
            return validMoves.get(value);
        }
        return new OthelloMove(game.getMark(), 8, 0);
    }

}
