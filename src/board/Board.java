package board;

public class Board {

	private int rows; //@ in _rows;
	private int cols; //@ in _cols;
	private Piece[][] pieces; //@ in _pieces;
	
	//@ public model int _rows;
    //@ private represents _rows = rows;
	//@ public model int _cols;
    //@ private represents _cols = cols;
	//@ public model Piece[][] _pieces;
    //@ private represents _pieces = pieces;
	
	// public invariant 0 < _rows < Integer.MAX_VALUE;
	// public invariant 0 < _cols < Integer.MAX_VALUE;
	
	//@ requires rows < 1 || cols < 1;
	//@ signals_only RuntimeException;
	//@ ensures false;
	//@ also
	//@ requires rows >= 1 && cols >= 1;
	//@ requires rows < Integer.MAX_VALUE && cols < Integer.MAX_VALUE;
	//@ ensures _rows == rows;
	//@ ensures _cols == cols;
	//@ signals_only \nothing;
	//@ ensures true;
	public Board (int rows, int cols) {
		if (rows < 1 || cols < 1) {
			throw new BoardException("Error creating board: there must be at least 1 row and 1 column");
		}
		this.rows = rows;
		this.cols = cols;
		pieces = new Piece[rows][cols];
	}
	
	//@ ensures \result == _rows;
	public int getRows() {
		return rows;
	}
	
	//@ ensures \result == _cols;
	public int getCols() {
		return cols;
	}
	
	//@ ensures \result == _pieces;
	public Piece[][] getPieces(){
		return pieces;
	}

	//@ requires 0 <= col;
	//@ requires 0 <= row;
	//@ ensures \result == _pieces[row][col];
	public /*@ non_null */ Piece getPiece(int row, int col) {
		if (!positionExists(new Position(row, col))) {
			throw new BoardException("Erro to get the piece: The position don't exists");
		}
		
		return pieces[row][col];
	}
	
	//@ requires 0 <= position.getRow();
	//@ requires 0 <= position.getColumn();
	public /*@ non_null */ Piece getPiece(Position position) {
		if (!positionExists(position)) {
			throw new BoardException("Erro to get the piece: The position: "+ position + " don't exists");
		}
		
		return pieces[position.getRow()][position.getColumn()];
	}
	
	public void placePiece(Piece piece, Position position) {
		if (!positionExists(position)) {
			throw new BoardException("Erro to place the piece: The position: "+ position + " don't exists");
		} else if (haveAPiece(position)) {
			throw new BoardException("Erro to place the piece: The position: "+ position + " already have a piece");
		}
		pieces[position.getRow()][position.getColumn()] = piece;
		piece.position = position;
	}
	
	//@ requires 0 <= position.getRow() < _rows;
	//@ requires 0 <= position.getColumn() < _cols;
	//@ requires haveAPiece(position);
	//@ ensures _pieces[position.getRow()][position.getColumn()] == null;
	//@ ensures \result instanceof Piece;
	//@ ensures \result != null;
	//@ ensures true;
	public Piece removePiece(Position position) {
		if (!positionExists(position)) {
			throw new BoardException("Erro to place the piece: The position: "+ position + " don't exists");
		}
		if (!haveAPiece(position)) {
			return null;
		}
		Piece aux = getPiece(position);
		aux.position = null;
		pieces[position.getRow()][position.getColumn()] = null;
		return aux;
	}
	
	// requires 0 <= position.getRow() < _rows;
	// requires 0 <= position.getColumn() < _cols;
	// ensures \result == true;
	// also
	// requires position.getRow() >= _rows || position.getRow() < 0;
	// requires position.getColumn() >= _cols || position.getColumn() < 0;
	// ensures \result == false;
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
