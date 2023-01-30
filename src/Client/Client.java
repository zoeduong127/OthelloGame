package Client;

import AI.ComputerPlayer;
import AI.NaiveStrategy;
import AI.SmartStrategy;
import Client.Model.ClientState;
import Client.Model.Command;
import Client.Model.GameOver;
import UI.HumanPlayer;
import model.*;

import java.io.IOException;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.Locale;
import static Client.Model.Command.*;

public class Client implements Runnable{
    private  ChatListener listener;
    public final ClientTUI TUI;
    private static final String Description = "Server from client center";
    private static final String SEND_COMMAND = "[CLIENT] ";
    public static final String SERVER_MESS = "[SERVER] ";
    private Socket socket;
    private boolean running;
    private PrintWriter pr ;
    private ClientState state;
    private AbstractPlayer player;
    private String username;
    private OthelloGame game;
    private String  decision;

    public Client (){
        this.TUI = new ClientTUI();
        this.running = false;
        this.state = ClientState.CONNECT_AWAITING;
    }

    /**
     *
     * @param address
     * @param port
     * @return
     */
    public boolean connect(InetAddress address, int port){
        try{
            this.socket = new Socket(address,port);
            this.pr = new PrintWriter(socket.getOutputStream(),true);
            sendCommand(Command.HELLO, Description);
            setState(ClientState.HELLO_AWAITING);
            TUI.println(SERVER_MESS+ "Connected succesfully");
            running = true;
            new Thread(this).start();
            return true;
        } catch (IOException e) {
            e.printStackTrace();
            return false;
        }
    }
    @Override
    public void run() {
        while(running){
            this.listener = new ChatListen(this, socket);
            new Thread((Runnable)listener).start();
        }
    }
    public void close(){
        try{
            this.socket.close();
            pr.close();
            this.running = false;
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void setState(ClientState state){
        this.state = state;
    }
    public  void sendMessage(String mess){
        pr.println(mess);
    }

    public  void sendCommand(String command, String desripton){
        String mess = Protocol.sendCommand(command,desripton);
        sendMessage(mess);
        TUI.println(SEND_COMMAND+ mess);
    }
    public void sendCommand(String command){
        sendMessage(command);
        TUI.println(SEND_COMMAND+ command);
    }

    public synchronized void handleHello(){
        if(state.equals(ClientState.HELLO_AWAITING)){
            this.requestLogin();
        }
    }

    public synchronized void requestLogin(){
        try {
            TUI.println(SERVER_MESS+ "Welcome to Othell, please Enter your name? ");
            String username = TUI.reader.readLine();
            this.username = username;
            sendCommand(Command.LOGIN,username);
            setState(ClientState.LOGIN_AWAITING);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    public synchronized void handleLogin() throws IOException {
        TUI.println(SERVER_MESS+ "Login succesfull with username : "+ username);
        if(state.equals(ClientState.LOGIN_AWAITING)){
            setState(ClientState.DECISION);
            this.handleUserchoice();
        }
    }
    public synchronized void handleAreadyLoggedIn(String input){
        TUI.println(SERVER_MESS+"Username is already ! Please enter another username: ");
        this.requestLogin();
    }

    public synchronized void handleList(String input) throws IOException {
        String[] active = input.split(Protocol.SEPARATOR);
        TUI.println(SERVER_MESS+ "List of online players: ");
        for(int i = 1; i < active.length; i++){
            TUI.println(active[i]);
        }
        this.handleUserchoice();
    }
    public synchronized void handleNewGame(String input) throws IOException {
        String[] name = input.split(Protocol.SEPARATOR);
        if(state.equals(ClientState.NEWGAME_AWAITING)){
            boolean checkplayer = name[1].equals(username);
            String player2name = null;
            if(checkplayer){
                TUI.println(SERVER_MESS+"Your opponent is  "+ name[2] +"! Game start!");
                player2name = name[2];
                HumanPlayer player2 = new HumanPlayer(player2name);
                this.game = new OthelloGame(player, player2, new Board());
            }else{
                TUI.println(SERVER_MESS+ "Your opponent is  "+ name[2] +"! Game start!");
                player2name = name[1];
                HumanPlayer player1 = new HumanPlayer(player2name);
                this.game = new OthelloGame(player1, player, new Board());
            }
            System.out.println(game);
            if(game.getTurn() == player){
                this.makeMove();
                setState(ClientState.MOVE_AWAITING);
            }else{
                setState(ClientState.MOVE_AWAITING);
                TUI.println(SERVER_MESS+ "Waiting for your turn");
           }
        }
    }
    public synchronized void makeMove(){
        if(game.getTurn() == player) {
            if(game.getValidMoves().size() != 0) {
                OthelloMove move = player.determineMove(game);
                int number = move.getRow() * 8 + move.getCol();
                sendCommand(Command.MOVE, Integer.toString(number));
            }else{
                sendCommand(Command.MOVE, "64");
            }
        }
    }
    public synchronized void handleMove(String a){
        String[] input = a.split(Protocol.SEPARATOR);
        if(state.equals(ClientState.MOVE_AWAITING)){
            if(!input[1].equals("64")) {
                int row = Integer.parseInt(input[1]) / 8;
                int col = Integer.parseInt(input[1]) % 8;
                OthelloMove move = new OthelloMove(game.getMark(), row, col);
                this.game.doMove(move);
                System.out.println(game);
                if (game.getTurn() == player) {
                    this.makeMove();
                } else {
                    TUI.println(SEND_COMMAND+ "Wait for your turn");
                }
            }else {
                game.turn += 1;
            }
        }
    }
    public synchronized void handleGameover(String[] arguments) throws IOException {
        String winner = SERVER_MESS+ "Congratulation "+arguments[2]+ " are winner \n";
        switch (arguments[1]) {
            case GameOver.VICTORY:
                if (arguments[2].equals(username)) {
                    TUI.println(SERVER_MESS+ "You are WINNER");
                } else {
                    TUI.println(SERVER_MESS+ "Gook luck later !");
                }
                break;
            case GameOver.DISCONNECT:
                TUI.println(SERVER_MESS+ "Your opponent disconnected "+ winner);
                break;
            case GameOver.DRAW:
                TUI.println(SERVER_MESS+ "Dras ! No winner!");
                break;
        }
        setState(ClientState.DECISION);
        this.handleUserchoice();
    }
    public synchronized void handleQuit() throws IOException {
        TUI.println(SERVER_MESS+ "Server will disconnect");
        this.close();
    }
    public synchronized void handleError(String input){
        if(input.equals(MOVE)){
            makeMove();
        }
    }
    public synchronized void handleUserchoice() throws IOException {
        this.printHelp();
        String choice = TUI.reader.readLine().toUpperCase();
        boolean commandValid = false;
        while (!commandValid) {
            switch (choice) {
                case Command.QUEUE:
                    TUI.println(SEND_COMMAND+ "Do you want AI to replace you ? Type YES or NO");
                    decision = TUI.reader.readLine().toUpperCase(Locale.ROOT);
                    switch (decision){
                        case "YES":
                            TUI.println(SEND_COMMAND+ " Choose Native (-N) / Smart (-S)");
                            String AI = TUI.reader.readLine().toUpperCase();
                            switch (AI) {
                                case "-N":
                                    player = new ComputerPlayer(new NaiveStrategy());
                                    break;
                                case "-S":
                                    player = new ComputerPlayer(new SmartStrategy());
                                    break;
                            }
                            break;
                        default:
                            player = new HumanPlayer(username);
                            break;
                    }
                    sendCommand(Command.QUEUE);
                    setState(ClientState.NEWGAME_AWAITING);
                    commandValid = true;
                    break;
                case Command.LIST:
                    sendCommand(LIST);
                    commandValid = true;
                    break;
                case Command.HELP:
                    this.printHelp();
                    commandValid = true;
                    break;
                case Command.QUIT:
                    handleQuit();
                    commandValid = true;
                    break;
                default:
                    System.out.println(SEND_COMMAND+ "ERROR: command " + choice + " is not a valid choice.");
                    this.printHelp();
                    choice = TUI.reader.readLine().toUpperCase();
                    break;
            }
        }
    }

    private void printHelp() {
        final String helpMenu = String.format("\nWHAT DO YOU WANT ?  ")+
                        String.format(" [QUEUE] JOIN A NEW GAME"
                                        +"\n [LIST] LIST OF ACTIVE PLAYERS"
                                        +"\n [HELP] PRINT THE HELP MENU"
                                        +"\n [QUIT] LOG OUT");
        TUI.println(helpMenu);
    }

}
