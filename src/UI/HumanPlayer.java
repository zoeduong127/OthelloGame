package UI;

import model.*;

import java.util.Locale;
import java.util.Scanner;
import model.AbstractPlayer;

public class HumanPlayer extends AbstractPlayer {
    public String input;
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
        System.out.println("Enter move: !(Enter number 127 to get hint)");
        input = s.nextLine();
        if(input.equals("127")){
            int row = game.getValidMoves().get(0).getRow();
            int col = game.getValidMoves().get(0).getCol();
            String index = null;
            switch(col){
                case 0: index = "A"+row;break;
                case 1: index = "B"+row;break;
                case 2: index = "C"+row;break;
                case 3: index = "D"+row;break;
                case 4: index = "E"+row;break;
                case 5: index = "F"+row;break;
                case 6: index = "G"+row;break;
                case 7: index = "H"+row;break;
            }
            
            System.out.println("HINT : "+ index);
        }
        int row = Integer.parseInt(String.valueOf(input.charAt(1)));
        int col = 0;
        String coll;
        switch(coll = String.valueOf(input.charAt(0)).toUpperCase(Locale.ROOT)){
            case "A": col = 0;break;
            case "B": col = 1;break;
            case "C": col = 2;break;
            case "D": col = 3;break;
            case "E": col = 4;break;
            case "F": col = 5;break;
            case "G": col = 6;break;
            case "H": col = 7;break;
        }
        String mark = ((OthelloGame) game).getMark();
        move = new OthelloMove(mark, row, col);
        }while(!game.isValidMove((OthelloMove) move));
        return (OthelloMove) move;
    }
}
