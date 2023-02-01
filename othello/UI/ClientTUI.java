package UI;

import Client.Client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Locale;

import static Client.Command.*;
import static Client.Protocol.*;

/**
 * TUI to get all input from player to client
 */

public class ClientTUI {
    private final PrintWriter print;
    public static BufferedReader reader;
    Client client;
    public ClientTUI(Client client){
        print = new PrintWriter(System.out, true);
        reader = new BufferedReader(new InputStreamReader(System.in));
        this.client = client;
    }

    /**
     * Print some string to screen
     * @param string the content want to print to screen
     */
    public void println(String string){
        print.println(string);
    }
    
    
    /**
     * Print the help menu for user to choose.
     */
    public void printHelp(){
        final String helpMenu = String.format("\nWHAT DO YOU WANT ?  ")+
                String.format(" \n [QUEUE] JOIN A NEW GAME"
                        +"\n [LIST] LIST OF ACTIVE PLAYERS"
                        +"\n [HELP] PRINT THE HELP MENU"
                        +"\n [QUIT] LOG OUT");
        println(helpMenu);
    }

    /**
     * Handle request from player by print the menu first and send content of request to player
     * If player want to join a game. Ask player whenever they want an AI to play instead of them and set player role as your choice
     * default for request which is not listed
     * @throws IOException if I/O occurs when handling with user's choice.
     */


    public synchronized void handleUserchoice() throws IOException {
        printHelp();
        String choice = reader.readLine().toUpperCase();
        boolean commandValid = false;
        while (!commandValid) {
            switch (choice) {
                case QUEUE:
                    client.setupPlayer();
                    client.sendCommand(QUEUE);
                    client.setState(ClientState.NEWGAME_AWAITING);
                    commandValid = true;
                    break;
                case LIST:
                    client.sendCommand(LIST);
                    commandValid = true;
                    break;
                case HELP:
                    printHelp();
                    commandValid = true;
                    break;
                case QUIT:
                    client.handleQuit();
                    commandValid = true;
                    break;
                default:
                    println(Clientmess(ERROR + " Wrong request ! Please try again !"));
                    printHelp();
                    choice = reader.readLine().toUpperCase();
                    break;
            }
        }
    }

    /**
     * get IP of server adress from input
     * @return the IP of server address
     * @throws IOException if I/O error occurs when read input
     */
    //@ ensures \result instanceof InetAddress;
    
    public InetAddress getIp() throws IOException {
        println("Enter the server address: ");
        String serverAddress = reader.readLine();
        InetAddress ip = InetAddress.getByName(serverAddress);
         return ip;
    }

    /**
     * get IP of server adrress from input
     * @return the port number tp connect server
     * @throws IOException if I/O error occurs when read input
     */
    //@ ensures \result instanceof Integer;
    public int getPort() throws IOException {
        println("Enter the port: ");
        int serverPort = 0;
        try {
            serverPort = Integer.parseInt(reader.readLine());
        }catch(NumberFormatException e){
            getPort();
        }
        return serverPort;
    }

    /**
     * get a string answer of a question from player
     * @param question is question client want to ask player
     * @return a string answer
     * @throws IOException if I/O error occurs when read input
     */
    //@ requires question != null;
    //@ ensures \result instanceof String;
    public String getString(String question) throws IOException {
        println(question);
        String decision = reader.readLine().toUpperCase(Locale.ROOT);
        return decision;
    }

    /**
     * get a string answer of a question from player
     * @param question is question client want to ask player
     * @return a boolean answer
     * @throws IOException if I/O error occurs when read input
     */
    //@ requires question != null;
    //@ ensures \result instanceof boolean;
    public boolean getBoolean(String question) throws IOException {
        println(question);
        String decision = reader.readLine().toUpperCase();
        return decision.equals("YES");
    }

    /**
     * Try to connect the server by given ip and port number
     * @throws IOException if I/O error occurs when read input
     */

    public void start() throws IOException {
        try {
            if (!client.connect(getIp(), getPort())) {
                println("\n ERROR: Failed to connect! Try again.");
                start();
            }
        }catch(UnknownHostException e){
            println("\n ERROR: Failed to find the Server Address! Try again.");
            start();
        }
    }
}
