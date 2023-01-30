package AI;

import model.Game;
import model.Move;
import model.OthelloGame;
import model.OthelloMove;

import java.util.List;
import java.util.Random;
/**
 * Implements the Strategy interface to define a Naive Strategy.
 */
public class NaiveStrategy implements Strategy {
    private String name;

    public NaiveStrategy() {
        this.name = "Naive Strategy";
    }
    public NaiveStrategy(String name){this.name = name;}
    /**
     * Getter for the name of the Strategy.
     * @return String name of the Strategy
     */
    public String getName() {
        return name;
    }

    /**
     * Determines the move to be played by the Naive Strategy.
     * @param game The instance of TicTacToeGame that is being played
     * @return Move selected randomly from the currently available moves.
     */

    @Override
    public OthelloMove determineMove(OthelloGame game) {
        List<OthelloMove> validMoves = game.getValidMoves();
        if(validMoves.size() > 0) {
            Random rand = new Random();
            int value = rand.nextInt(game.getValidMoves().size());
            return validMoves.get(value);
        }
        return new OthelloMove(game.getMark(), 7, 8);
    }


}
