package AI;

import model.*;

public class ComputerPlayer extends AbstractPlayer {
    public Strategy getStrategy() {
        return strategy;
    }

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    private Strategy strategy;
    private String mark;

    public ComputerPlayer(String mark, Strategy strategy) {
        super(strategy.getName() + " - " + mark);
        this.strategy = strategy;
        this.mark = mark;
    }
    public ComputerPlayer(Strategy strategy){
        super(strategy.getName());
        this.strategy = strategy;
    }

    public OthelloMove determineMove(OthelloGame game) {
        return strategy.determineMove(game);
    }
}
