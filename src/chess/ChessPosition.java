package chess;

import board.Position;

public class ChessPosition {
	private char col;
	private int row;
	
	//@ requires col < 'a' || col > 'h' || row < 1 || row > 8;
	//@ signals_only ChessException;
	//@ ensures false;
	//@ also
	//@ requires col >= 'a' && col <= 'h' && row >= 1 && row <= 8;
	//@ ensures this.col == col;
	//@ ensures this.row == row;
	//@ ensures true;
	public ChessPosition(int row, char col) {
		if (col < 'a' || col > 'h' || row < 1 || row > 8) 
			throw new ChessException("Erro instantiating ChessPosition: Valid value only from a1 to h8.");
		this.col = col;
		this.row = row;
	}

	//@ ensure /result == this.col;
	public char getCol() {
		return col;
	}

	public void setCol(char col) {
		this.col = col;
	}

	//@ ensure /result == this.row;
	public int getRow() {
		return row;
	}

	public void setRow(int row) {
		this.row = row;
	}
	
	protected Position toPosition() {
		return new Position(8 - row, col - 'a');
	}
	
	public static ChessPosition fromPosition(Position position) {
		return new ChessPosition (8 - position.getRow(), (char) ('a' + position.getColumn()));
	}
	
	@Override
	public String toString() {
		return "" + col + row;
	}
}
