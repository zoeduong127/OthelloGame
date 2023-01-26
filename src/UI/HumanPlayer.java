package UI;

import model.*;

import java.util.Scanner;
import model.AbstractPlayer;

public class HumanPlayer extends AbstractPlayer {
    public HumanPlayer(String name) {

        super(name);
    }

    /**
     *
     * @param game the current game
     * @return valid move
     */

    public OthelloMove determineMove(OthelloGame game) {
        Move move = null;
        do{
        Scanner s = new Scanner(System.in);
        System.out.println("Enter move: ");
        String input = s.nextLine();
        String[] number = input.split(",");
        int row = Integer.parseInt(number[0]);
        int col = Integer.parseInt(number[1]);
        String mark = ((OthelloGame) game).getMark();
        move = new OthelloMove(mark, row, col);
        }while(!game.isValidMove((OthelloMove) move));


        return (OthelloMove) move;
    }
}
