package board;

public class Position {

	private Integer row;
	private Integer col;
	
	// public invariant 0 < row < Integer.MAX_VALUE;
	// public invariant 0 < col < Integer.MAX_VALUE;
	
	//@ pure
	public Position (int row, int col) {
		this.row = row;
		this.col = col;
	}

	//@ pure
	public Integer getRow() {
		return row;
	}

	//@ requires row >= 0;
	public void setRow(Integer row) {
		this.row = row;
	}

	//@ pure
	public Integer getColumn() {
		return col;
	}

	//@ requires col >= 0;
	public void setColumn(Integer col) {
		this.col = col;
	}
	
	//@ requires row >= 0;
	//@ requires col >= 0;
	public void setPositions(int row, int col) {
		this.row = row;
		this.col = col;
	}
	
	@Override
	public String toString() {
		return row + "/" + col;
	}
}
