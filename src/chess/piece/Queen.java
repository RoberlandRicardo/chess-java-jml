package chess.piece;

import board.Board;
import board.Piece;
import board.Position;
import chess.Color;

public class Queen extends Piece{
	
	//@ public normal_behavior
	//@ pure
	public Queen(Board board, Color color) {
		super(board, color);
		
	}
	
	//@ also
	//@ ensures \result == "Q";
	@Override
	public /*@ non_null */ String toString() {
		return "Q";
	}
	
	@Override
	public boolean[][] possibleMoves(){
		boolean[][] aux = new boolean[super.getBoard().getRows()][super.getBoard().getCols()];
		
		Position p = new Position(0,0);
		
		// Norte
		p.setColumn(position.getColumn());
		//@ maintaining 0 <= i <= position.getRow();
		//@ loop_assigns aux[*][*];
		//@ decreases i;
		for (int i = position.getRow() - 1; i >= 0; i--) {
			p.setRow(i);
			if (getBoard().haveAPiece(p)) {
				if (isOpponentPiece(p)) {
					aux[p.getRow()][p.getColumn()] = true;
				}
				break;
			} else {
				aux[p.getRow()][p.getColumn()] = true;
			}
		}
		
		// Leste
		p.setRow(position.getRow());
		//@ maintaining 0 <= i <= position.getColumn();
		//@ loop_assigns aux[*][*];
		//@ decreases i;
		for (int i = position.getColumn() - 1; i >= 0; i--) {
			p.setColumn(i);
			if (getBoard().haveAPiece(p)) {
				if (isOpponentPiece(p)) {
					aux[p.getRow()][p.getColumn()] = true;
				}
				break;
			} else {
				aux[p.getRow()][p.getColumn()] = true;
			}
		}
		
		// Sul
		p.setColumn(position.getColumn());
		//@ maintaining position.getRow() + 1 <= i <= getBoard().getRows();
		//@ loop_assigns aux[*][*];
		//@ decreases getBoard().getRows() - i;
		for (int i = position.getRow() + 1; i < getBoard().getRows(); i++) {
			p.setRow(i);
			if (getBoard().haveAPiece(p)) {
				if (isOpponentPiece(p)) {
					aux[p.getRow()][p.getColumn()] = true;
				}
				break;
			} else {
				aux[p.getRow()][p.getColumn()] = true;
			}
		}
		
		// Oeste
		p.setRow(position.getRow());
		//@ maintaining position.getColumn() + 1 <= i <= getBoard().getCols();
		//@ loop_assigns aux[*][*];
		//@ decreases getBoard().getCols() - i;
		for (int i = position.getColumn() + 1; i < getBoard().getCols(); i++) {
			p.setColumn(i);
			if (getBoard().haveAPiece(p)) {
				if (isOpponentPiece(p)) {
					aux[p.getRow()][p.getColumn()] = true;
				}
				break;
			} else {
				aux[p.getRow()][p.getColumn()] = true;
			}
		}
		
		//Noroeste
		p.setPositions(position.getRow() - 1, position.getColumn() - 1);;
		while (getBoard().positionExists(p)) {
			if (getBoard().haveAPiece(p)) {
				if (getBoard().getPiece(p).getColor() == super.getColor()) {
					break;
				} else {
					aux[p.getRow()][p.getColumn()] = true;
					break;
				}
			} else {
				aux[p.getRow()][p.getColumn()] = true;
				p.setPositions(p.getRow()-1, p.getColumn()-1);
			}
		}
		
		//Sudoeste
		p.setPositions(position.getRow() + 1, position.getColumn() - 1);;
		while (getBoard().positionExists(p)) {
			if (getBoard().haveAPiece(p)) {
				if (getBoard().getPiece(p).getColor() == super.getColor()) {
					break;
				} else {
					aux[p.getRow()][p.getColumn()] = true;
					break;
				}
			} else {
				aux[p.getRow()][p.getColumn()] = true;
				p.setPositions(p.getRow()+1, p.getColumn()-1);
			}
		}
		
		//Sudeste
		p.setPositions(position.getRow() + 1, position.getColumn() + 1);;
		while (getBoard().positionExists(p)) {
			if (getBoard().haveAPiece(p)) {
				if (getBoard().getPiece(p).getColor() == super.getColor()) {
					break;
				} else {
					aux[p.getRow()][p.getColumn()] = true;
					break;
				}
			} else {
				aux[p.getRow()][p.getColumn()] = true;
				p.setPositions(p.getRow()+1, p.getColumn()+1);
			}
		}
		
		//Nordeste
		p.setPositions(position.getRow() - 1, position.getColumn() + 1);;
		while (getBoard().positionExists(p)) {
			if (getBoard().haveAPiece(p)) {
				if (getBoard().getPiece(p).getColor() == super.getColor()) {
					break;
				} else {
					aux[p.getRow()][p.getColumn()] = true;
					break;
				}
			} else {
				aux[p.getRow()][p.getColumn()] = true;
				p.setPositions(p.getRow()-1, p.getColumn()+1);
			}
		}
		return aux;
	}
}
