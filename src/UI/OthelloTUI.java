package UI;

import AI.ComputerPlayer;

import AI.NaiveStrategy;
import AI.SmartStrategy;
import model.*;

import javax.swing.*;
import java.util.Scanner;

import static model.Mark.XX;

public class OthelloTUI extends JPanel {
    public void run() {
        boolean running = true;
        Scanner s = new Scanner(System.in);
        while (running) {
            AbstractPlayer player1;
            AbstractPlayer player2;

            System.out.print("Enter Player 1 name: ");
            String name1 = s.nextLine();

            switch (name1) {
                case "-N": player1 = new ComputerPlayer(Mark.XX.getSymbol(), new NaiveStrategy()); break;
                case "-S": player1 = new ComputerPlayer(Mark.XX.getSymbol(), new SmartStrategy()); break;
                default: player1 = new HumanPlayer(name1);
            }

            System.out.print("Enter Player 2 name: ");
            String name2 = s.nextLine();

            switch (name2) {
                case "-N": player2 = new ComputerPlayer(Mark.OO.getSymbol(), new NaiveStrategy()); break;
                case "-S": player2 = new ComputerPlayer(Mark.OO.getSymbol(), new SmartStrategy()); break;
                default: player2 = new HumanPlayer(name2);
            }

            Game game = new OthelloGame(player1, player2, new Board());

            while (true) {
                System.out.println(game);
                System.out.println("Player 1 - Black square - Please enter <col+row>");
                Move nextMove = player1.determineMove((OthelloGame) game);
                game.doMove((OthelloMove) nextMove);

                if (game.isGameOver()) {
                    break;
                }

                System.out.println(game);
                System.out.println("Player 2 - White square - Please enter <col+row>");
                nextMove = player2.determineMove((OthelloGame) game);
                game.doMove((OthelloMove) nextMove);

                if (game.isGameOver()) {
                    break;
                }
            }
            System.out.println(game);
            if (game.getWinner() != null) {
                try {
                    System.out.printf("%s wins!\n", ((HumanPlayer) game.getWinner()).getName());
                } catch (Exception e) {
                    System.out.printf("%s wins!\n", ((ComputerPlayer) game.getWinner()).getName());
                }
            } else {
                System.out.println("Draw.\n");
            }

            System.out.print("Press any key to play again (0 to quit): ");
            if (s.next().equals("0")) {
                running = false;
            }
        }
    }

    public void strategy1v1() {
        System.out.println("----------------\nAI Battles\nNaive (-N), Smart (-S)\n----------------");
        boolean running = true;
        while (running) {
            AbstractPlayer player1;
            AbstractPlayer player2;
            Scanner s = new Scanner(System.in);
            System.out.print("Enter number of trials: ");
            int trials = s.nextInt();

            while (true) {
                boolean validName = true;

                System.out.print("AI 1: ");
                String ai1 = s.next();
                switch (ai1) {
                    case "-N": player1 = new ComputerPlayer(Mark.XX.getSymbol(), new NaiveStrategy()); break;
                    case "-S": player1 = new ComputerPlayer(Mark.XX.getSymbol(), new SmartStrategy()); break;
                    default: player1 = new ComputerPlayer(Mark.XX.getSymbol(), new NaiveStrategy()); validName = false;
                }

                System.out.print("AI 2: ");
                String ai2 = s.next();
                switch (ai2) {
                    case "-N": player2 = new ComputerPlayer(Mark.OO.getSymbol(), new NaiveStrategy()); break;
                    case "-S": player2 = new ComputerPlayer(Mark.OO.getSymbol(), new SmartStrategy()); break;
                    default: player2 = new ComputerPlayer(Mark.OO.getSymbol(), new NaiveStrategy()); validName = false;
                }
                if (validName) {
                    break;
                } else {
                    System.out.println("Invalid input.");
                }
            }

            int player1Wins = 0;
            int player2Wins = 0;
            int draws = 0;

            for (int i = 0; i < trials; i++) {
                Game game = new OthelloGame(player1, player2,new Board());

                while (true) {
                    Move nextMove = player1.determineMove((OthelloGame) game);
                    game.doMove((OthelloMove) nextMove);

                    if (game.isGameOver()) {
                        break;
                    }

                    nextMove = player2.determineMove((OthelloGame) game);
                    game.doMove((OthelloMove) nextMove);

                    if (game.isGameOver()) {
                        break;
                    }
                }

                if (game.getWinner() != null) {
                    if (game.getWinner() == player1) {
                        player1Wins++;
                    } else {
                        player2Wins++;
                    }
                } else {
                    draws++;
                }
            }
            System.out.printf("Player 1 wins: %s\nPlayer 2 wins: %s\nDraws: %s\n", player1Wins, player2Wins, draws);
            System.out.println("Press any key to go again, 0 to quit: ");
            String again = s.next();
            if (again.equals("0")) {
                running = false;
            }
        }
    }

    public static void main(String[] args) {
        OthelloTUI tui = new OthelloTUI();
        Scanner s = new Scanner(System.in);
        boolean running = true;
        while (running) {
            System.out.print("----------------\nOthello\n----------------\n1: Play Othello\n2: AI Only \n0: Quit\n\nEnter command: ");
            int command = s.nextInt();
            switch (command) {
                case 0: running = false; break;
                case 1: tui.run(); break;
                case 2: tui.strategy1v1(); break;
                default:
                    System.out.println("Invalid command");
                    running = false;
                    break;
            }
        }
    }
}