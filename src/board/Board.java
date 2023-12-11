package board;

public class Board {

	//@ spec_public
	private int rows;
	//@ spec_public
	private int cols;
	//@ spec_public
	private /*@ nullable */ Piece /*@ non_null */[][] pieces;

	//@ 	requires rows < 1 || cols < 1;
	//@ 	signals_only BoardException;
	//@ 	ensures false;
	//@ 	requires 0 < rows < Integer.MAX_VALUE;
	//@ 	requires 0 < cols < Integer.MAX_VALUE;
	//@ 	ensures pieces.length == rows;
	//@ 	ensures this.rows == rows;
	//@ 	ensures this.cols == cols;
	//@ pure
	public Board(int rows, int cols) {
		if (rows < 1 || cols < 1) {
			throw new BoardException("Error creating board: there must be at least 1 row and 1 column");
		}
		this.rows = rows;
		this.cols = cols;
		pieces = new Piece[rows][cols];
	}
	
	//@ ensures \result == rows;
	//@ pure
	public int getRows() {
		return rows;
	}
	
	//@ ensures \result == cols;
	//@ pure
	public int getCols() {
		return cols;
	}

	//@ ensures \result == pieces;
	//@ pure
	public Piece[][] getPieces() {
		return pieces;
	}

	//@ requires 0 <= col <= 7;
	//@ requires 0 <= row <= 7;
	//@ requires pieces.length >= 1;
	//@ requires pieces[0].length >= 1;
	//@ requires row < pieces.length;
	//@ requires col < pieces[0].length;
	//@ ensures \result == pieces[row][col];
	//@ pure
	public /*@ non_null */ Piece getPiece(int row, int col) {
		if (!positionExists(new Position(row, col))) {
			throw new BoardException("Erro to get the piece: The position don't exists");
		}
		return pieces[row][col];
	}
	
	//@ requires 0 <= position.getRow();
	//@ requires 0 <= position.getColumn();
	//@ pure
	public /*@ non_null */ Piece getPiece(Position position) {
		if (!positionExists(position)) {
			throw new BoardException("Erro to get the piece: The position: " + position + " don't exists");
		}

		return pieces[position.getRow()][position.getColumn()];
	}

	public void placePiece(Piece piece, Position position) {
		if (!positionExists(position)) {
			throw new BoardException("Erro to place the piece: The position: " + position + " don't exists");
		} else if (haveAPiece(position)) {
			throw new BoardException("Erro to place the piece: The position: " + position + " already have a piece");
		}
		pieces[position.getRow()][position.getColumn()] = piece;
		piece.position = position;
	}

	//@ requires 0 <= position.getRow() < rows;
	//@ requires 0 <= position.getColumn() < cols;
	//@ requires haveAPiece(position);
	//@ ensures pieces[position.getRow()][position.getColumn()] == null;
	//@ ensures \result instanceof Piece;
	//@ ensures \result.getPosition() == null;
	//@ ensures \result != null;
	//@ ensures true;
	public /*@ non_null */  Piece removePiece(Position position) {
		if (!positionExists(position)) {
			throw new BoardException("Erro to place the piece: The position: " + position + " don't exists");
		}
		if (!haveAPiece(position)) {
			return null;
		}
		Piece aux = getPiece(position);
		aux.position = null;
		pieces[position.getRow()][position.getColumn()] = null;
		return aux;
	}

	//@ requires 0 <= position.getRow();
	//@ requires 0 <= position.getColumn();
	//@ requires position.getColumn() < cols;
	//@ ensures \result == true;
	//@ pure
	public boolean positionExists(Position position) {
		return position.getRow() >= 0 && position.getRow() < rows
				&& position.getColumn() >= 0 && position.getColumn() < cols;
	}

	//@ requires position != null;
	//@ ensures \result == true;
	//@ also
	//@ requires position == null;
	//@ ensures \result == false;
	//@ pure
	public boolean haveAPiece(Position position) {
		return getPiece(position) != null;
	}
}
