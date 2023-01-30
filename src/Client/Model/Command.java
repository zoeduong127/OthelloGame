package Client.Model;

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
}
