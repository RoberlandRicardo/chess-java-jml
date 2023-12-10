package chess;


import java.security.InvalidParameterException;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import board.Board;
import board.Piece;
import board.Position;
import chess.piece.*;

public class ChessMatch {

	//@ spec_public
	private int turn;
	//@ spec_public
	private /* non_null */ Color currentPlayer;
	//@ spec_public
	private /* non_null */ Board board;
	//@ spec_public
	private boolean check;
	//@ spec_public
	private boolean checkMate;
	//@ spec_public
	private Piece promoted;
	//@ spec_public
	private Piece enPassantVunerable;
	
	private List<Piece> piecesOnTheBoard = new ArrayList<>();
	private List<Piece> capturedPieces = new ArrayList<>();
	
	// public invariant 1 <= turn;
	
	//@ ensures \result == this.turn;
	public int getTurn() {
		return turn;
	}
	
	//@ ensures \result == this.currentPlayer;
	public Color getCurrentPlayer() {
		return currentPlayer;
	}
	
	//@ ensures \result == this.check;
	public boolean getCheck() {
		return check;
	}
	
	//@ ensures \result == this.checkMate;
	public boolean getCheckMate() {
		return checkMate;
	}
	
	//@ ensures \result == this.promoted;
	public Piece getPromoted() {
		return promoted;
	}
	
	//@ ensures \result == this.enPassantVunerable;
	public Piece getEnPassantVunerable() {
		return enPassantVunerable;
	}
	
	public Piece[][] getPieces(){
		return board.getPieces();
	}
	
	//@ ensures board != null;
	//@ ensures this.turn == 1;
	//@ ensures this.currentPlayer == Color.WHITE;
	//@ pure
	public ChessMatch() {
		board = new Board(8,8);
		turn = 1;
		currentPlayer = Color.WHITE;
		initialSetup();
	}

	//@ requires sourcePosition.toPosition() == null;
	//@ ensures false;
	//@ also
	//@ requires sourcePosition.toPosition() != null;
	//@ requires !board.positionExists(sourcePosition.toPosition()) || !board.haveAPiece(sourcePosition.toPosition()) || currentPlayer != board.getPiece(sourcePosition.toPosition()).getColor() || !board.getPiece(sourcePosition.toPosition()).havePossibleMove();
	//@ signals_only ChessException;
	//@ ensures false;
	//@ also
	//@ requires sourcePosition.toPosition() != null;
	//@ requires board.positionExists(sourcePosition.toPosition());
	//@ requires board.haveAPiece(sourcePosition.toPosition());
	//@ requires currentPlayer == board.getPiece(sourcePosition.toPosition()).getColor();
	//@ requires board.getPiece(sourcePosition.toPosition()).havePossibleMove();
	//@ ensures true;
	public boolean[][] possibleMoves(/* non_null */ ChessPosition sourcePosition){
		Position source = sourcePosition.toPosition();
		if (!board.positionExists(source)) {
			throw new ChessException("Error in the source position: This position are invalid");
		}
		if (!board.haveAPiece(source)) {
			throw new ChessException("Error in the source position: There is no piece in the original position");
		}
		if (currentPlayer != board.getPiece(source).getColor()) {
			throw new ChessException("Error in the source position: The chosen piece is not yours");
		}
		if (!board.getPiece(source).havePossibleMove()) {
			throw new ChessException("Error in the source position: There is no possible moves for the piece");
		}
		return board.getPiece(source).possibleMoves();
	}
	
	
	public Piece chessMove(ChessPosition sourcePosition, ChessPosition targetPosition) {
		Position source = sourcePosition.toPosition();
		Position target = targetPosition.toPosition();

		if (!board.getPiece(source).possibleMove(target)) {
			throw new ChessException("Error in the target position: This move is invalid");
		}
		Piece capturedPiece = makeMove(source,target);
		
		if (testCheck(currentPlayer)) {
			undoMove(source, target, capturedPiece);
			throw new ChessException("You cant put yourself in check");
		}
		
		Piece movedPiece = board.getPiece(target);
		
		
		// Promoted move
		promoted = null;
		if (movedPiece instanceof Pawn) {
			if ((movedPiece.getColor() == Color.WHITE && target.getRow() == 0) ||(movedPiece.getColor() == Color.BLACK && target.getRow() == 7)) {
				promoted = board.getPiece(target);
				promoted = replacePromotedPiece("Q");
			}
		}
		
		check = (testCheck(getOpponent(currentPlayer))) ? true : false;
		if (testCheckMate(getOpponent(currentPlayer))) {
			checkMate = true;
		} else {
			nextTurn();
		}
		
		// En passant move
		if (movedPiece instanceof Pawn && (target.getRow() == source.getRow() - 2 || target.getRow() == source.getRow() + 2 )) {
			enPassantVunerable = movedPiece;
		} else {
			enPassantVunerable = null;
		}
		
		return capturedPiece;
	}
	
	//@ requires promoted == null;
	//@ signals_only IllegalStateException;
	//@ ensures false;
	//@ also
	//@ requires !type.equals("B") && !type.equals("N") && !type.equals("R") && !type.equals("Q");
	//@ signals_only InvalidParameterException;
	//@ ensures false;
	//@ also
	//@ requires type.equals("P");
	//@ requires promoted != null;
	//@ ensures !(\result instanceof Pawn);
	//@ ensures \result == board.getPiece(promoted.getChessPosition().toPosition());
	public Piece replacePromotedPiece(/* non_null */ String type) {
		if (promoted == null) {
			throw new IllegalStateException("No have to be promoted");
		}
		if (!type.equals("B") && !type.equals("N") && !type.equals("R") && !type.equals("Q")) {
			throw new InvalidParameterException("Invalid type for promotion");
		}
		
		Position pos = promoted.getChessPosition().toPosition();
		Piece p = board.removePiece(pos);
		piecesOnTheBoard.remove(p);
		
		Piece newPiece = newPiece(type, promoted.getColor());
		board.placePiece(newPiece, pos);
		piecesOnTheBoard.add(newPiece);
		
		return newPiece;
	}
	
	//@ requires type.equals("B");
	//@ ensures \result instanceof Bishop;
	//@ ensures \result.getColor() == color;
	//@ also
	//@ requires type.equals("N");
	//@ ensures \result instanceof Knight;
	//@ ensures \result.getColor() == color;
	//@ also
	//@ requires type.equals("Q");
	//@ ensures \result instanceof Queen;
	//@ ensures \result.getColor() == color;
	//@ also
	//@ requires type.equals("R");
	//@ ensures \result instanceof Rook;
	//@ ensures \result.getColor() == color;
	private Piece newPiece(String type, Color color) {
		if (type.equals("B")) return new Bishop(board, color);  
		if (type.equals("N")) return new Knight(board, color);  
		if (type.equals("Q")) return new Queen(board, color);  
		return new Rook(board, color);  
	}

	//@ requires board.haveAPiece(source);
	//@ ensures board.getPiece(source).getMoveCount() == 1 + \old(board.getPiece(source).getMoveCount());
	//@ also
	//@ requires board.haveAPiece(source);
	//@ requires board.haveAPiece(target);
	//@ ensures board.getPiece(source).getMoveCount() == 1 + \old(board.getPiece(source).getMoveCount());
	//@ ensures capturedPieces.get(capturedPieces.size()).equals(target);
	private Piece makeMove(Position source, Position target) {
		Piece p = board.removePiece(source);
		p.increaseMoveCount();
		Piece capturedPiece = board.removePiece(target);
		
		board.placePiece(p, target);
		
		if (capturedPiece != null) {
			piecesOnTheBoard.remove(capturedPiece);
			capturedPieces.add(capturedPiece);
		}
		
		// Enpassant move
		if (p instanceof Pawn) {
			if (source.getColumn() != target.getColumn() && capturedPiece == null) {
				Position pawnPosition;
				if (p.getColor() == Color.WHITE) {
					pawnPosition = new Position(target.getRow() + 1, target.getColumn());
				} else {
					pawnPosition = new Position(target.getRow() - 1, target.getColumn());
				}
				capturedPiece = board.removePiece(pawnPosition);
				capturedPieces.add(capturedPiece);
				piecesOnTheBoard.remove(capturedPiece);
			}
		}
		
		// Roque move
		// King' sides
		if (p instanceof King && target.getColumn() == source.getColumn() + 2) {
			Position sourceT = new Position(source.getRow(), source.getColumn()+3);
			Position targetT = new Position(source.getRow(), source.getColumn()+1);
			Piece rook = board.removePiece(sourceT);
			board.placePiece(rook, targetT);
			rook.increaseMoveCount();
		}
		// Queen' sides
		if (p instanceof King && target.getColumn() == source.getColumn() - 2) {
			Position sourceT = new Position(source.getRow(), source.getColumn()-4);
			Position targetT = new Position(source.getRow(), source.getColumn()-1);
			Piece rook = board.removePiece(sourceT);
			board.placePiece(rook, targetT);
			rook.increaseMoveCount();
		}
		
		return capturedPiece;
	}
	
	
	private void undoMove(Position source, Position target, Piece capturedPiece) {
		Piece p = board.removePiece(target);
		p.decreaseMoveCount();
		board.placePiece(p, source);
		
		if (capturedPiece != null) {
			board.placePiece(capturedPiece, target);
			capturedPieces.remove(capturedPiece);
			piecesOnTheBoard.add(capturedPiece);
		}
		
		// Roque move
		// King' sides
		if (p instanceof King && target.getColumn() == source.getColumn() + 2) {
			Position sourceT = new Position(source.getRow(), source.getColumn()+3);
			Position targetT = new Position(source.getRow(), source.getColumn()+1);
			Piece rook = board.removePiece(targetT);
			board.placePiece(rook, sourceT);
			rook.decreaseMoveCount();
		}
		// Queen' sides
		if (p instanceof King && target.getColumn() == source.getColumn() - 2) {
			Position sourceT = new Position(source.getRow(), source.getColumn()-4);
			Position targetT = new Position(source.getRow(), source.getColumn()-1);
			Piece rook = board.removePiece(targetT);
			board.placePiece(rook, sourceT);
			rook.decreaseMoveCount();
		}
		
		// Enpassant move
		if (p instanceof Pawn) {
			if (source.getColumn() != target.getColumn() && capturedPiece == enPassantVunerable) {
				Piece pawn = board.removePiece(target);
				Position pawnPosition;
				if (p.getColor() == Color.WHITE) {
					pawnPosition = new Position(3, target.getColumn());
				} else {
					pawnPosition = new Position(4, target.getColumn());
				}
				board.placePiece(pawn, pawnPosition);
				
			}
		}
	}
	
	//@ ensures searchKing(color) != null;
	//@ pure
	private boolean testCheck(Color color) {
		Position kingPosition = searchKing(color).getChessPosition().toPosition();
		List<Piece> opponentPieces = piecesOnTheBoard.stream().filter(x -> x.getColor() == getOpponent(color)).collect(Collectors.toList());
		//@ maintaining 0 <= \count <= opponentPieces.size();
		//@ loop_writes \nothing;
		//@ decreases opponentPieces.size() - \count;
		for (Piece p : opponentPieces) {
			boolean[][] pos = p.possibleMoves();
			if (pos[kingPosition.getRow()][kingPosition.getColumn()]) {
				return true;
			}
		}
		return false;
	}
	
	//@ requires !testCheck(color);
	//@ ensures \result == false;
	//@ also
	//@ requires testCheck(color);
	private boolean testCheckMate(Color color) {
		if (!testCheck(color)) {
			return false;
		}
		List<Piece> list = piecesOnTheBoard.stream().filter(x -> x.getColor() == color).collect(Collectors.toList());
		for (Piece p : list) {
			boolean[][] mat = p.possibleMoves();
			
			//@ maintaining 0 <= i <= board.getRows();
			//@ decreases board.getRows() - i;
			for (int i = 0; i < board.getRows(); i++) {
				//@ maintaining 0 <= j <= board.getCols();
				//@ decreases board.getCols() - j;
				for (int j = 0; j < board.getCols(); j++) {
					if (mat[i][j]) {
						Position source = p.getChessPosition().toPosition();
						Position target = new Position(i,j);
						Piece capturedPiece = makeMove(source, target);
						boolean testCheck = testCheck(color);
						undoMove(source, target, capturedPiece);
						if (!testCheck) {
							return false;
						}
					}
				}
			}
		}
		return true;
	}
	
	//@ requires currentPlayer == Color.WHITE;
	//@ ensures turn == \old(turn) + 1;
	//@ ensures currentPlayer == Color.BLACK;
	//@ also
	//@ requires currentPlayer == Color.BLACK;
	//@ ensures turn == \old(turn) + 1;
	//@ ensures currentPlayer == Color.WHITE;
	private void nextTurn() {
		turn++;
		currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
	}
	
	//@ requires color == Color.WHITE;
	//@ ensures \result == Color.BLACK;
	//@ also
	//@ requires color == Color.BLACK;
	//@ ensures \result == Color.WHITE;	
	private Color getOpponent(Color color) {
		return (color == color.WHITE) ? Color.BLACK : Color.WHITE;
	}
	
	//@ ensures \result instanceof King;
	//@ pure
	private Piece searchKing(Color color) {
		List<Piece> list = piecesOnTheBoard.stream().filter(x -> x.getColor() == color).collect(Collectors.toList());
		//@ maintaining 0 <= \count <= list.size();
		//@ maintaining \forall int k; 0 <= k < \count; !(list.get(k) instanceof King);
		//@ loop_writes \nothing;
		//@ decreases list.size() - \count;
		for (Piece p : list) {
			if (p instanceof King) {
				return p;
			}
		}
		throw new IllegalStateException("There is no " + color + " king on the board");
	}
	
	//@ requires 0 <= col <= 7;
	//@ requires 0 <= col <= 7;
	//@ ensures board.getPiece(row, col) != null;
	//@ ensures piecesOnTheBoard.size() > 0;
	private void placeNewPiece(char col, int row, /* non_null */ Piece piece) {
		board.placePiece(piece, new ChessPosition(row, col).toPosition());
		piecesOnTheBoard.add(piece);
	}
	
	private void initialSetup() {
		placeNewPiece('h', 1, new Rook(board, Color.WHITE));
        placeNewPiece('a', 1, new Rook(board, Color.WHITE));
        placeNewPiece('g', 1, new Knight(board, Color.WHITE));
        placeNewPiece('b', 1, new Knight(board, Color.WHITE));
        placeNewPiece('e', 1, new King(board, Color.WHITE, this));
        placeNewPiece('d', 1, new Queen(board, Color.WHITE));
        placeNewPiece('a', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('b', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('c', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('d', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('e', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('f', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('g', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('h', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('c', 1, new Bishop(board, Color.WHITE));
        placeNewPiece('f', 1, new Bishop(board, Color.WHITE));
        
        placeNewPiece('a', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('b', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('c', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('d', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('e', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('f', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('g', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('h', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('h', 8, new Rook(board, Color.BLACK));
        placeNewPiece('a', 8, new Rook(board, Color.BLACK));
        placeNewPiece('e', 8, new King(board, Color.BLACK, this));
        placeNewPiece('d', 8, new Queen(board, Color.BLACK));
        placeNewPiece('g', 8, new Knight(board, Color.BLACK));
        placeNewPiece('b', 8, new Knight(board, Color.BLACK));
        placeNewPiece('c', 8, new Bishop(board, Color.BLACK));
        placeNewPiece('f', 8, new Bishop(board, Color.BLACK));
	}
}
