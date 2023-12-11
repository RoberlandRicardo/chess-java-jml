package board;

import chess.ChessPosition;
import chess.Color;

public abstract class Piece {
	//@ spec_public
	protected Position position;
	//@ spec_public
	private Board board;
	//@ spec_public
	private Color color;
	//@ spec_public
	private int moveCount;
	
	//@ public normal_behavior
	//@ 	ensures this.board == board;
	//@ 	ensures this.color == color;
	//@ 	ensures this.position == null;
	//@ pure
	public Piece(/*@ non_null */ Board board,/*@ non_null */ Color color) {
		this.board = board;
		this.color = color;
		position = null;

		//@ assert position == null;
	}
	
	//@ ensures \result == board;
	//@ pure
	public Board getBoard() {
		return board;
	}
	
	//@ ensures \result == color;
	//@ pure
	public Color getColor() {
		return color;
	}
	
	//@ ensures \result == moveCount;
	//@ pure
	public int getMoveCount() {
		return moveCount;
	}
	
	//@ requires this.moveCount < Integer.MAX_VALUE;
	//@ ensures this.moveCount == \old(this.moveCount) + 1;
	public void increaseMoveCount() {
		this.moveCount++;
	}
	
	//@ requires this.moveCount > 0;
	//@ ensures this.moveCount == \old(this.moveCount) - 1;
	public void decreaseMoveCount() {
		this.moveCount--;
	}
	
	//@ ensures \result == ChessPosition.fromPosition(position);
	//@ pure
	public ChessPosition getChessPosition() {
		return ChessPosition.fromPosition(position);
	}
	
	//@ pure
	public abstract boolean[][] possibleMoves();
	
	//@ ensures \result == possibleMoves()[position.getRow()][position.getColumn()];
	//@ pure
	public boolean possibleMove(Position position) {
		return possibleMoves()[position.getRow()][position.getColumn()];
	}
	
	//@ requires possibleMoves() != null;
	//@ ensures true;
	//@ pure
	public boolean havePossibleMove() {
		boolean[][] aux = possibleMoves();
		for (int i = 0; i < aux.length; i++) {
			for (int j = 0; j < aux[0].length; j++) {
				if (aux[i][j]) return true;
			}
		}
		return false;
	}
	//@ requires position != null;
	protected boolean isOpponentPiece(Position position) {
		Piece p = board.getPiece(position);
		return p != null && p.getColor() != color; 
	}

	//@ ensures \result == position;
    //@ pure
	public Position getPosition() {
		return position;
	}
}
