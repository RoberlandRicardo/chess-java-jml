package chess;

import board.Position;

public class ChessPosition {
	//@ spec_public
	private char col;
	//@ spec_public
	private int row;
	
	// public invariant 0 <= row <= 7;
	// public invariant 0 <= col <= 7;
	
	//@ requires col < 'a' || col > 'h' || row < 1 || row > 8;
	//@ signals_only ChessException;
	//@ ensures false;
	//@ also
	//@ requires col >= 'a' && col <= 'h' && row >= 1 && row <= 8;
	//@ ensures this.col == col;
	//@ ensures this.row == row;
	//@ ensures true;
	//@ pure
	public ChessPosition(int row, char col) {
		if (col < 'a' || col > 'h' || row < 1 || row > 8) 
			throw new ChessException("Erro instantiating ChessPosition: Valid value only from a1 to h8.");
		this.col = col;
		this.row = row;
	}

	//@ ensures \result == this.col;
	public char getCol() {
		return col;
	}

	//@ ensures this.col == col;
	//@ assignable this.col;
	public void setCol(char col) {
		this.col = col;
	}

	//@ ensures \result == this.row;
	public int getRow() {
		return row;
	}

	//@ ensures this.row == row;
	//@ assignable this.row;
	public void setRow(int row) {
		this.row = row;
	}
	
	//@ spec_public
	//@ pure
	protected Position toPosition() {
		return new Position(8 - row, col - 'a');
	}
	
	//@ requires position.getColumn() instanceof Integer;
	//@ requires 7 >= position.getColumn() >= 0;
	//@ requires position.getRow() instanceof Integer;
	//@ requires 7 >= position.getRow() >= 0;
	//@ pure
	public static ChessPosition fromPosition(Position position) {
		return new ChessPosition (8 - position.getRow(), (char) ('a' + position.getColumn()));
	}
	
	//@ also 
	//@ ensures \result instanceof String;
	//@ pure
	@Override
	public String toString() {
		return "" + col + row;
	}
}
