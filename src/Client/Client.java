package Client;

import Player.AI.ComputerPlayer;
import Player.AI.NaiveStrategy;
import Player.AI.SmartStrategy;
import Player.Human.AbstractPlayer;
import Player.Human.HumanPlayer;
import model.MainGame.Board;
import model.MainGame.OthelloGame;
import model.Move.Move;
import model.Move.OthelloMove;

import java.io.IOException;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.NoRouteToHostException;
import java.net.Socket;
import java.net.SocketException;

import static Client.Command.*;
import static Client.Protocol.*;

/**
 * Client is class working directly with player and server.
 * Receive and handler request from player and message from server to display for player.
 * One play is a client object
 *
 */
public class Client implements Runnable{
    public final ClientTUI TUI;
    private Socket socket;
    private boolean running;
    private PrintWriter pr ;
    private ClientState state;
    private AbstractPlayer player;
    private String username;
    private OthelloGame game;


    public Client (){
        this.TUI = new ClientTUI(this);
        this.running = false;
        this.state = ClientState.CONNECT_AWAITING;
    }

    /**
     * Attempts to connect to a server at the given address and port.
     * @param address The address of the server to connect to.
     * @param port The port on the server to connect to.
     * @return True if the connection was successful, false otherwise.
     */
    //@ requires address != null && 0<= port && port <= 65500;
    //@ensures \result <==> state == ClientState.HELLO_AWAITING && running == true && socket.getInetAddress().equals(address) && socket.getLocalPort() == port;
    public boolean connect(InetAddress address, int port){
        try{
            this.socket = new Socket(address,port);
            this.pr = new PrintWriter(socket.getOutputStream(),true);
            sendCommand(Command.HELLO, Description);
            setState(Protocol.ClientState.HELLO_AWAITING);
            TUI.println(Servermess("Connected succesfully"));
            running = true;
            new Thread(this).start();
            return true;
        } catch (NoRouteToHostException e){
            TUI.println(" Some problems with your connection ! Please check your Internet and try again");
            return false;
        } catch (IOException e) {
            TUI.println(Command.ERROR + "Some problem in reading input");
            return false;
        }
    }
    /**
     * Receive for incoming messages from the server as long as the connection to the server is active.
     * This method creates a new thread for each incoming message to be handled by the `Listener` class.
     */
    @Override
    public void run() {
        while(running){
            Listen listener = new Listener(this, socket);
            new Thread((Runnable) listener).start();
        }
    }

    /**
     * This method sets the `running` false to stop the listening loop in the `run` method.
     * Closes the connection to the server, including the socket and the print writer.
     */
    //@ensures socket.isClosed() == true && running == false;
    public void close(){
        try{
            this.running = false;
            this.socket.close();
            pr.close();
        } catch(SocketException e){
            System.exit(0);
        } catch (IOException e) {
            TUI.println(Command.ERROR + " Some problem in reading input");
        }
    }

    /**
     * Sets the current state of the client.
     * @param state The new state of the client.
     */
    /*@ requires state != null;
        ensures this.state == state;
    */

    public void setState(ClientState state){
        this.state = state;
    }

    /**
     * Sends a message to the server.
     * @param mess The message to be sent.
     */
    //@ requires mess != null;
    public void sendMessage(String mess){
        pr.println(mess);
    }


    /**
     * Sends a command to the server with a description.
     * @param command The command to be sent.
     * @param descripton The description of the command.
     */
    /*@
      requires command != null && descripton != null;
      requires Protocol.sendCommand(command, descripton) != null;
    */
    public void sendCommand(String command, String descripton){
        String mess = Protocol.sendCommand(command,descripton);
        sendMessage(mess);
        TUI.println(SEND_COMMAND+ mess);
    }


    /**
     * Sends a command to the server.
     * @param command The command to be sent.
     */
    //@ requires command != null;
    public void sendCommand(String command){
        sendMessage(command);
        TUI.println(SEND_COMMAND+ command);
    }


    /**
     * Handles the "HELLO" message from the server.
     * Requests the login if the client is in the HELLO_AWAITING state.
     */
    /*@
        requires state != null;
        ensures state.equals(ClientState.HELLO_AWAITING) ==> (\old(state) == ClientState.HELLO_AWAITING) && (this.state == ClientState.LOGIN_AWAITING);
    */
    public synchronized void handleHello(){
        if(state.equals(ClientState.HELLO_AWAITING)){
            this.requestLogin();
        }
    }

    /**
     * Get username from player and send a request login with this username to server
     * Afterward,setting the state of player to "LOGIN_AWAITING".
     */

    //@ ensures this.state == ClientState.LOGIN_AWAITING;
    public synchronized void requestLogin(){
        try {
            String username = TUI.getString(Servermess("Welcome to Othell, please Enter your name? "));
            this.username = username;
            sendCommand(Command.LOGIN,username);
            setState(ClientState.LOGIN_AWAITING);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    /**
     * Handles the successful login of a client by printing a success message with the username and setting the client's state to "DECISION".
     * Then it invokes the handleUserchoice method.
     * @throws IOException if an I/O error occurs when the client is communicating with the server.
     */
    //@ ensures state == ClientState.LOGIN_AWAITING ==> this.state == ClientState.DECISION;
    public synchronized void handleLogin() throws IOException {
        TUI.println(Servermess("Login succesfull with username : "+ username));
        if(state.equals(ClientState.LOGIN_AWAITING)){
            setState(ClientState.DECISION);
            TUI.handleUserchoice();
        }
    }
    /**
     * Handles the situation where a client tries to log in with an already used username.
     * Prints a message asking the client to enter another username and invokes the requestLogin method.
     * @param input the input string sent by the client that triggered this method.
     */
    //@requires input != null;
    //@requires input.startsWith(Command.ALREADYLOGGEDIN);

    public synchronized void handleAreadyLoggedIn(String input){
        TUI.println(Servermess("Username is already ! Please enter another username: "));
        this.requestLogin();
    }

    /**
     * Handles the list of online players by splitting the input string using the character "~" separator,
     * Printing the list of players, and then invoking the handleUserchoice method.
     * @param input the input string sent by the client that triggered this method.
     * @throws IOException if an I/O error occurs when the client is communicating with the server.
     */
    //@requires input != null;
    //@requires input.startsWith(Command.LIST);
    public synchronized void handleList(String input) throws IOException {
        String[] active = input.split(Protocol.SEPARATOR);
        TUI.println(Servermess("List of online players: "));
        for(int i = 1; i < active.length; i++){
            TUI.println(active[i]);
        }
        TUI.handleUserchoice();
    }

    /**
     * Handles the start of a new game by parsing the input string, checking the client's state,
     * and creating a new Othello game with two HumanPlayer instances.
     * Then it prints the name of the opponent and starts the game by either making a move or waiting for the other player's turn.
     * @param input the input string sent by the client that triggered this method.
     */
    /*@
        requires state == ClientState.NEWGAME_AWAITING;
        requires input != null;
        requires input.startsWith(Command.NEWGAME);
        requires input.split(Protocol.SEPARATOR).length == 3;
        requires player != null;
        requires game == null;
        ensures state == ClientState.MOVE_AWAITING;
        ensures (\exists HumanPlayer p; p.getName().equals(input.split(Protocol.SEPARATOR)[1]) || p.getName().equals(input.split(Protocol.SEPARATOR)[2]));
        ensures game != null;
    @*/
    public synchronized void handleNewGame(String input){
        String[] name = input.split(Protocol.SEPARATOR);
        if(state.equals(ClientState.NEWGAME_AWAITING)){
            boolean checkplayer = name[1].equals(username);
            String player2name;
            if(checkplayer){
                TUI.println(Servermess("Your opponent is  "+ name[2] +"! Game start!"));
                player2name = name[2];
                HumanPlayer player2 = new HumanPlayer(player2name);
                this.game = new OthelloGame(player, player2, new Board());
            }else{
                TUI.println(Servermess("Your opponent is  "+ name[1] +"! Game start!"));
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
                TUI.println(Servermess( "Waiting for your turn"));
           }
        }
    }

    /**
     * Makes a move in the current game if it's the client's turn and there are valid moves available.
     * The move is determined by the player's determineMove method and sent to the server using the sendCommand method.
     * If there are no valid moves, the method sends a MOVE command with the value "64" to the server.
     */
    /*@ requires game != null && player != null;
      @ ensures ((\forall Move move ;game.isValidMove(move); player.determineMove(game) == move));
      @*/
    public synchronized void makeMove(){
        if(game.getTurn().equals(player)) {
            Move move = player.determineMove(game);
            int number = move.getRow() * 8 + move.getCol();
            sendCommand(Command.MOVE, Integer.toString(number));
        }else{
            TUI.println("Wait for your turn");
        }
    }

    /**
     * Handles move which is sent from server by checking the client state first
     * after parsing from string to row and col, do this move and display the board game again.
     * Then check the next turn to decide making a move or waiting for the other player's turn.
     * @param a the input string is sent from server to client.
     */
    /*@ requires a != null && state != null && game != null && player != null;
        ensures (state.equals(ClientState.MOVE_AWAITING) ==>(game.getTurn() == player <==>(\old(game.getTurn() != player))));
        ensures game.getTurn() != \old(game.getTurn());
  @*/

    public synchronized void handleMove(String a){
        String[] input = a.split(Protocol.SEPARATOR);
        if(state.equals(ClientState.MOVE_AWAITING)){
            int row = Integer.parseInt(input[1]) / 8;
            int col = Integer.parseInt(input[1]) % 8;
            OthelloMove move = new OthelloMove(game.getMark(), row, col);
            this.game.doMove(move);
            System.out.println(game);
            if(this.game.isGameOver()){
                TUI.println("Game Over");
                return;
            };
            if (game.getTurn() == player) {
                this.makeMove();
            } else {
                TUI.println(Clientmess("Wait for your turn"));
            }
        }
    }

    /**
     * Handles game over which is sent from server by checking the reason of game over first
     * @param input message from server is split by listener
     * @throws IOException if an I/O error occurs when the client is communicating with the server.
     */
    /*@
      requires input != null;
      requires input.startsWith(Command.GAMEOVER);
      requires game.isGameOver() == true;
      ensures state == ClientState.DECISION && state != \old(state);
    */
    public synchronized void handleGameover(String input) throws IOException {
        String[] arguments = input.split(SEPARATOR);
        switch (arguments[1]) {
            case Command.VICTORY:
                if (arguments[2].equals(username)) {
                    TUI.println(Servermess("\nCongratulation You are winner "));
                } else {
                    TUI.println(Servermess("Gook luck later !"));
                }
                break;
            case Command.DISCONNECT:
                String winner = Servermess("\nCongratulation Your are winner ");
                TUI.println(Servermess("Your opponent disconnected " + winner));
                break;
            case Command.DRAW:
                TUI.println(Servermess("Draw ! No winner!"));
                break;
        }
        setState(ClientState.DECISION);
        TUI.handleUserchoice();
    }
    /**
     * Disconnect to server and close the socket because player want to log out of game .
     */
    //@ ensures socket.isClosed() == false;
    //@ ensures running == false;
    public synchronized void handleQuit(){
        TUI.println(Servermess("Server will disconnect"));
        System.exit(0);
        this.close();
    }


    /**
     * Handles errors encountered during the game.
     * @param input The input that caused the error.
     */
    /*@
      requires input != null;
      requires input.startsWith(Command.ERROR);
    */
    public synchronized void handleError(String input){
        String[] error = input.split(SEPARATOR);
        if(error[1].equals(MOVE)){
            makeMove();
        }
    }

    /**
     * Ask player what role they want to be ( Smart AI/ Native AI/ Human Player).
     * Set player as your request.
     * @throws IOException if I/O occurs during reading process from input .
     */
    /*@ requires username != null;
        ensures (player instanceof ComputerPlayer ||player instanceof ComputerPlayer || player instanceof HumanPlayer);
     @*/
    public void setupPlayer() throws IOException {
        boolean decision = TUI.getBoolean(Clientmess("Do you want AI to replace you ? Type YES or NO"));
        if(decision) {
            String choice = TUI.getString(Clientmess("Choose Native (-N) / Smart (-S)"));
            if (choice.equals("-N")) {
                player = new ComputerPlayer(new NaiveStrategy(username));
            } else {
                player = new ComputerPlayer(new SmartStrategy(username));
            }
        }else{
            player = new HumanPlayer(username);
        }
    }

    /**
     *Connect player to server by enter address and number of port
     * @throws IOException if I/O occurs when reading data from command
     */
    public static void main(String[] args) throws IOException {
        Client client = new Client();
        client.TUI.start();
    }

}
