package Player.Human;

import model.MainGame.Game;
import model.Move.Move;
import model.Move.OthelloMove;

import java.util.Locale;
import java.util.Scanner;

public class HumanPlayer extends AbstractPlayer {
    private String input;
    private int row;
    private int col;
    private Move move;


    public HumanPlayer(String name) {
        super(name);
    }

    /**
     * Get index of move from play parse to 2-dimensional index and check whenever valid move.
     * In other hand, if this player doesn't have any valid moves, player will enter A8 to pass your turn
     * @param game the current game
     * @return valid move
     */

    public Move determineMove(Game game) {
        if(game.getValidMoves().size() == 0){
            System.out.println("Don't have any valid move ! Your turn will pass !");
            move = new OthelloMove(game.getMark(),8, 0);
            return move;
        }else {
            Scanner s = new Scanner(System.in);
            System.out.println("Please enter <col+row> (ex: A0 = index 0)");
            System.out.println("Enter move: !(Enter number 127 to get hint)");
            input = s.nextLine();
            //Get hint
            if (input.equals("127")) {
                this.row = game.getValidMoves().get(0).getRow();
                this.col = game.getValidMoves().get(0).getCol();
                String index = null;
                switch (col) {
                    case 0:
                        index = "A" + row;
                        break;
                    case 1:
                        index = "B" + row;
                        break;
                    case 2:
                        index = "C" + row;
                        break;
                    case 3:
                        index = "D" + row;
                        break;
                    case 4:
                        index = "E" + row;
                        break;
                    case 5:
                        index = "F" + row;
                        break;
                    case 6:
                        index = "G" + row;
                        break;
                    case 7:
                        index = "H" + row;
                        break;
                }
                System.out.println("HINT : " + index);
                return determineMove(game);
            }else{
                // No get hint
                move = rightMove(game);
                if (!game.isValidMove(move)) {
                    System.out.println("[ERROR] Is not valid move ! Please enter another Move");
                    determineMove(game);
                }
                return move;
            }
        }
    }
    public Move rightMove(Game game){
        Move move;
        //check whenever right a number
        try {
            row = Integer.parseInt(String.valueOf(input.charAt(1)));
        }catch(NumberFormatException e) {
            System.out.println("[ERROR] Wrong syntax move ! Please try again");
            determineMove(game);
        }
        // Convert from character to a number
        String coll = String.valueOf(input.charAt(0)).toUpperCase(Locale.ROOT);
        switch (coll) {
            case "A":
                col = 0;
                break;
            case "B":
                col = 1;
                break;
            case "C":
                col = 2;
                break;
            case "D":
                col = 3;
                break;
            case "E":
                col = 4;
                break;
            case "F":
                col = 5;
                break;
            case "G":
                col = 6;
                break;
            case "H":
                col = 7;
                break;
            default:
                System.out.println("[ERROR] ! Wrong syntax move! Please try again");
                determineMove(game);
                break;
        }
        String mark = game.getMark();
        move = new OthelloMove(mark, row, col);
        return move;
    }
}
