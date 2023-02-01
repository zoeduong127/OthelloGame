package Client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import java.net.SocketException;

/**
 * A class that listens to incoming messages from a server and calls the appropriate
 * method on the client to handle the message.
 */
public class Listener implements Listen, Runnable{
    private final Socket socket;
    private final Client client;
    private BufferedReader reader;
    public Listener(Client client, Socket socket){
        this.socket = socket;
        this.client = client;
    }

    /**
     * Handles incoming messages from the server.
     * @param input The message received from the server.
     * @throws IOException If an I/O error occurs while reading from the socket.
     * @throws ProtocolException If the message received from the server is not recognized as a valid command.
     */
    @Override
    public synchronized void handleMessage(String input) throws IOException, ProtocolException {
        String[] split = input.split(Protocol.SEPARATOR);
        switch(split[0]){
            case Command.HELLO:
                client.handleHello();
                break;
            case Command.LOGIN:
                client.handleLogin();
                break;
            case Command.ALREADYLOGGEDIN:
                client.handleAreadyLoggedIn(input);
                break;
            case Command.NEWGAME:
                client.TUI.println(Protocol.SERVER_MESS+ input);
                client.handleNewGame(input);
                break;
            case Command.MOVE:
                client.TUI.println(Protocol.SERVER_MESS+ input );
                client.handleMove(input);
                break;
            case Command.GAMEOVER:
                client.TUI.println(input);
                client.handleGameover(input);
                break;
            case Command.LIST:
                client.handleList(input);
                break;
            case Command.ERROR:
                client.TUI.println(Protocol.SERVER_MESS+ input);
                client.handleError(input);
                break;
            default:
                throw new ProtocolException("Server send a unknown command: "+ input);
        }
    }
    /**
     * Listens to incoming messages from the server and calls the handleMessage method to process the message.
     * If an I/O error occurs, the connection to the server will be closed.
     */

    @Override
    public void run() {
        while (true) {
            try {
                reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                String line;
                while ((line = reader.readLine()) != null) {
                    handleMessage(line);
                }
                reader.close();
            } catch (SocketException e) {
                client.TUI.println("Lost connection ! Please reload ");
                client.close();
                System.exit(0);
            } catch (IOException e) {
                client.close();
            } catch (ProtocolException e) {
                e.printStackTrace();
                client.close();
            }
        }
    }
}
