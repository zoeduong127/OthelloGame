package AI;

import model.Game;
import model.Move;
import model.OthelloGame;
import model.OthelloMove;

public interface Strategy {
    /**
     * Returns the name of particular strategy.
     * @return String name of strategy
     */
    //@ensures \result!= null;
    String getName();

    /**
     * Determines which move will be played next in the current game.
     * @param game The instance of TicTacToeGame that is being played
     * @return Move which is played next
     */
    //@requires game != null;
//    Move determineMove(Game game);

    OthelloMove determineMove(OthelloGame game);
}
