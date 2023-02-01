package Client;

/**
 * This interface is a collection of Command from client send to server and vice versa
 */
public interface Command {
    String HELLO = "HELLO";
    String LOGIN = "LOGIN";
    String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    String QUEUE = "QUEUE";
    String NEWGAME = "NEWGAME";
    String MOVE = "MOVE";
    String QUIT = "QUIT";
    String GAMEOVER = "GAMEOVER";
    String HELP = "HELP";
    String LIST = "LIST";
    String ERROR = "ERROR";
    String VICTORY = "VICTORY";
    String DISCONNECT = "DISCONNECT";
    String DRAW = "DRAW";
}
