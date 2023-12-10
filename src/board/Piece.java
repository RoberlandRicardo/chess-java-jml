package board;

import chess.ChessPosition;
import chess.Color;

public abstract class Piece {
	protected Position position;
	private Board board;
	private Color color;
	private int moveCount;
	
	// @ ensures this.board == board;
	// @ ensures this.color == color;
	// @ ensures this.position == null;
	// @ pure
	public Piece(/*@ non_null */ Board board,/*@ non_null */ Color color) {
		this.board = board;
		this.color = color;
		position = null;
	}
	
	public Board getBoard() {
		return board;
	}
	
	//@ pure
	public Color getColor() {
		return color;
	}
	
	//@ pure
	public int getMoveCount() {
		return moveCount;
	}
	
	public void increaseMoveCount() {
		this.moveCount++;
	}
	
	public void decreaseMoveCount() {
		this.moveCount--;
	}
	
	//@ pure
	public ChessPosition getChessPosition() {
		return ChessPosition.fromPosition(position);
	}
	
	public abstract boolean[][] possibleMoves();
	
	public boolean possibleMove(Position position) {
		return possibleMoves()[position.getRow()][position.getColumn()];
	}
	
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
	
	protected boolean isOpponentPiece(Position position) {
		Piece p = board.getPiece(position);
		return p != null && p.getColor() != color; 
	}
}
