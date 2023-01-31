package Player.AI;

import model.MainGame.Game;
import model.Move.Move;

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

    Move determineMove(Game game);
}
