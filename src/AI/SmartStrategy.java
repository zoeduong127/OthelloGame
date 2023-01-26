package AI;

import model.*;

import java.util.List;

/**
 * Implements the Strategy interface to define a Smart Strategy.
 */
public class SmartStrategy implements Strategy {
    private final int DEPTH = 5;
    private String name;

    public SmartStrategy() {
        this.name = "Smart Strategy";
    }

    /**
     * Getter for the name of the strategy.
     * @return String name of strategy
     */
    public String getName() {
        return name;
    }


    public OthelloMove getMove(OthelloGame game){
        return findWinningMove(game);
    }

    /**
     * Determines whether there is a move that instantly wins the game for the current player.
     * @param game The instance of TicTacToeGame which is being played
     * @return Move which wins the game, or null if no such move exists
     */
    public OthelloMove findWinningMove(OthelloGame game) {
        int bestValue = -1000;
        int alpha = -1000;
        int beta = 1000;
        OthelloMove bestMove = null;
        List<OthelloMove> moves = game.getValidMoves(Mark.XX.getSymbol());
        for(int i = 0; i < moves.size(); i ++){
            game.doMove(new OthelloMove(Mark.XX.getSymbol(), moves.get(i).getRow(), moves.get(i).getCol()));
            int value = Minimax(game,0,alpha,beta,false);
            game.doMove(new OthelloMove(Mark.EMPTY.getSymbol(),moves.get(i).getRow(), moves.get(i).getCol()));
            if(bestValue < value){
                bestValue = value;
                bestMove = moves.get(i);
            }
            alpha = Math.max(alpha, bestValue);
            if(beta <= alpha){
                break;
            }
        }
        return bestMove;
    }
    private int Minimax(OthelloGame game, int depth, int alpha, int beta, boolean b){
//        if(game.isGameOver() || depth == DEPTH){
//            return game.i;
//        }
        if(b){
            int best = -1000;
            List<OthelloMove> list = game.getValidMoves(Mark.XX.getSymbol());
            for(int i = 0; i < list.size(); i ++) {
                game.doMove(new OthelloMove(Mark.XX.getSymbol(), list.get(i).getRow(), list.get(i).getCol()));
                int value = Minimax(game, depth + 1, alpha, beta, false);
                game.doMove(new OthelloMove(Mark.EMPTY.getSymbol(), list.get(i).getRow(), list.get(i).getCol()));
                best = Math.max(best, value);
                alpha = Math.max(alpha, best);
                if(beta <= alpha) {
                    break;
                }
            }
            return best;
        }else{
            int best = 1000;
            List<OthelloMove> list = game.getValidMoves(Mark.OO.getSymbol());
            for(int i = 0; i < list.size(); i ++) {
                game.doMove(new OthelloMove(Mark.OO.getSymbol(), list.get(i).getRow(), list.get(i).getCol()));
                int value = Minimax(game, depth + 1, alpha, beta, true);
                game.doMove(new OthelloMove(Mark.EMPTY.getSymbol(), list.get(i).getRow(), list.get(i).getCol()));
                best = Math.max(best, value);
                alpha = Math.max(alpha, best);
                if(beta <= alpha) {
                    break;
                }
            }
            return best;
        }
    }

    /**
     * Determines which move should be played next by the Smart Strategy.
     * Uses the findWinningMove method and a deep copy of the game
     * to simulate playing moves for the AI and the player and determine
     * which move is best.
     * @param game The instance of TicTacToeGame that is being played
     * @return Move which wins the game instantly, move which stops enemy from winning
     * or random move if the former don't apply.
     */
    @Override
    public OthelloMove determineMove(OthelloGame game) {
          return getMove(game);
    }
}
