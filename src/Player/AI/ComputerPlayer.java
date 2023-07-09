package Player.AI;

import Player.Human.AbstractPlayer;
import model.MainGame.Game;
import model.Move.Move;
/**
 * The ComputerPlayer class represents a computer player in a board game.
 * The class extends the AbstractPlayer class and uses a strategy to determine its moves.
 **/

public class ComputerPlayer extends AbstractPlayer {
    private final Strategy strategy;
    private String mark;



    /**
     Constructs a new ComputerPlayer object with the specified mark and strategy.
     @param mark The mark of the computer player on the game board
     @param strategy The strategy used by the computer player to determine its moves
     */
    public ComputerPlayer(String mark, Strategy strategy) {
        super(strategy.getName() + " - " + mark);
        this.strategy = strategy;
        this.mark = mark;
    }
    /**
     * Constructs a new ComputerPlayer object with the specified strategy.
     * @param strategy The strategy used by the computer player to determine its moves
     */
    public ComputerPlayer(Strategy strategy){
        super(strategy.getName());
        this.strategy = strategy;
    }

    /**
     * Determines the next move of the computer player using its strategy.
     * @param game The game for which the computer player is determining its move
     * @return The next move of the computer player
     */
    //@ requires game != null;
    //@ ensures \result instanceof Move;
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }
}
