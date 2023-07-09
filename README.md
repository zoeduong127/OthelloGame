# Othello game

Othello is a classic game that is popular in all over the world. It is a two-players game played on a board 8x*, where each player tries to capture as many of the opponent's pieces on the board at the end of the game wins.

# Requirements
>This project requires Java ( IntellJ/ VScode) to set up.
>
>You need a strong internet connection.

# Usage
Below are the instructions for starting the online and offline game.

### Play game online 
#### Start the client
> Go to class _Client_ in the package _client_ and run the class.
> 
> Enter **130.89.253.64** if you are asked to enter the address of the server.
> 
> Enter port number **44444** if you are asked to enter the port number of the server.
>
>Enter random user number If you are asked to enter a username.
> 
> Enter **"QUEUE"** if you want to start a new game.

### Start the localgame
##### If you want to play a game.
> Go to class _OthelloUI_ in the package _UI_ and run the class.
> 
> Enter **1**
> 
>
> Firsly, you need to set up role for player 1.
> 
>Enter **"-S"** if you want first player is a smart AI and **"-N"** if you want first player is a native AI or **random username** if you want to be first player as a human.(the same with player 2)
>
>Secondly, you need to set up role for player 2 (The same as player 1).

##### If you want to play a game.
> Go to class _OthelloUI_ in the package _UI_ and run the class.
>
> Enter **2**
>
> Enter a number of trials you want to watch
> 
> Firstly, you need to set up role for AI 1.
>
>Enter **"-S"** if you want first player is a smart AI and **"-N"** if you want first player is a native AI
>
>Secondly, you need to set up role for AI 2 (The same as player 1).



# File Structure

* **Client** - this package includes  all files following the Model-View-Controller for the client side
* **model** - this package contains the classes that are responsible for how to run a Othello game( game logic, handle move, check game condition).
  * **MainGame** - this package contains Board, OthelloGame.
  * **Move** - this package contains mark, move with necessary attributes.
* **AI** - this package contains 2 AI and player to construct players for game
  * **AI** - this package stores 2 AI
  * **Human** - this package contains Player, Human Player and Abstract-player class.
* **test** - this package contains the test part of the game.