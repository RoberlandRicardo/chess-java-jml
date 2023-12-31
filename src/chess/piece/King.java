package chess.piece;

import board.Board;
import board.Piece;
import board.Position;
import chess.ChessMatch;
import chess.Color;

public class King extends Piece{
	
	private /*@ non_null */ ChessMatch match;
	
	//@ pure
	public King(Board board, Color color, ChessMatch match) {
		super(board, color);
		this.match = match;
		
	}
	
	//@ also
	//@ ensures \result == "K";
	@Override
	public  /*@ non_null */ String toString() {
		return "K";
	}
	
	
	//@ requires !(getBoard().getPiece(position) instanceof Rook);
	//@ ensures \result == false;
	//@ also
	//@ requires !(getBoard().getPiece(position).getColor() == getColor());
	//@ ensures \result == false;
	//@ also
	//@ requires !(getBoard().getPiece(position).getMoveCount() == 0);
	//@ ensures \result == false;
	private boolean testRookCanRoque(/*@ non_null */ Position position) {
		Piece p = getBoard().getPiece(position);
		return p != null && p instanceof Rook && p.getColor() == getColor() && p.getMoveCount() == 0;
	}
	
	@Override
	public boolean[][] possibleMoves(){
		boolean[][] aux = new boolean[super.getBoard().getRows()][super.getBoard().getCols()];
		//@ maintaining 0 <= position.getRow() - 1 <= i <= position.getRow() + 1 <= 7;
		//@ maintaining \count <= 3;
		//@ maintaining (\forall int k;  
		//@						position.getRow() - 1 <= k <= position.getRow() + 1;
		//@						(\forall int j;
		//@						position.getColumn() - 1 <= j <= position.getColumn() + 1;
		//@						((getBoard().getPiece(k,j) == null || getBoard().getPiece(k,j).getColor() != getColor())  
		//@						==> aux[k][j] == true)));
		//@ decreases 3 - i;
		for (int i = position.getRow() - 1; i <= position.getRow() + 1; i++) {
			//@ maintaining 0 <= position.getColumn() - 1 <= j <= position.getColumn() + 1 <= 7;
			//@ maintaining \count <= 3;
			//@ loop_assigns aux[*][*];
			//@ decreases 3 - j;
			for (int j = position.getColumn() - 1; j <= position.getColumn() + 1; j++) {
				if (!(i < 0 || i >= getBoard().getRows() || j < 0 || j >= getBoard().getCols())) {
					if (getBoard().getPiece(i,j) == null){
						aux[i][j] = true;
					} else {
						if (getBoard().getPiece(i,j).getColor() != getColor()) {
							aux[i][j] = true;
						}
					}
				}
			}
		}
		
		// Roque
		
		if (getMoveCount() == 0) {
			// King' sides
			Position p = new Position(position.getRow(), 7);
			if (testRookCanRoque(p)) {
				Position p1 = new Position(position.getRow(), 6);
				Position p2 = new Position(position.getRow(), 5);
				if (getBoard().getPiece(p1) == null && getBoard().getPiece(p2) == null) {
					aux[p.getRow()][6] = true;
				}
			}
			// Queen' sides
			p.setPositions(position.getRow(), 0);
			if (testRookCanRoque(p)) {
				Position p1 = new Position(position.getRow(), 3);
				Position p2 = new Position(position.getRow(), 2);
				Position p3 = new Position(position.getRow(), 1);
				if (getBoard().getPiece(p1) == null && getBoard().getPiece(p2) == null && getBoard().getPiece(p3) == null) {
					aux[p.getRow()][2] = true;
				}
			}
		}
		return aux;
	}
}
