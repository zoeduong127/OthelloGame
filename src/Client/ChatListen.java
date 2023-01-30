package Client;

import Client.Model.Command;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;

public class ChatListen implements ChatListener, Runnable{
    private Socket socket;
    private Client client;
    public ChatListen(Client client,Socket socket){
        this.socket = socket;
        this.client = client;
    }
    @Override
    public synchronized void handleMessage(String input) throws IOException {
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
                client.TUI.println(client.SERVER_MESS+ input);
                client.handleNewGame(input);
                break;
            case Command.MOVE:
                client.TUI.println(client.SERVER_MESS+ input );
                client.handleMove(input);
                break;
            case Command.GAMEOVER:
                client.handleGameover(split);
                break;
            case Command.LIST:
                client.handleList(input);
                break;
            case Command.ERROR:
                client.TUI.println(client.SERVER_MESS+ input);
                client.handleError(input);
                break;
            default:
                client.TUI.println("Server send a unknown command "+input);
                break;
        }
    }

    @Override
    public void run() {
        BufferedReader reader = null;
        try {
            reader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            String line;
            while((line = reader.readLine()) != null){
                handleMessage(line);
            }
        } catch (IOException e) {
            e.printStackTrace();
            client.close();
        }
    }
}
