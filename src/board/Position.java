package board;

public class Position {
	//@ spec_public
	private Integer row;
	//@ spec_public
	private Integer col;
	
	// public invariant 0 < row < Integer.MAX_VALUE;
	// public invariant 0 < col < Integer.MAX_VALUE;
	
	//@ public normal_behavior
	//@ 	requires 0 < row < Integer.MAX_VALUE;
	//@ 	requires 0 < col < Integer.MAX_VALUE;
	//@ 	ensures this.row == row;
	//@ 	ensures this.col == col;
	//@ pure
	public Position (int row, int col) {
		this.row = row;
		this.col = col;
	}

	//@ ensures \result == row;
	//@ pure
	public Integer getRow() {
		return row;
	}

	//@ requires row >= 0;
	//@ ensures this.row == row;
	public void setRow(Integer row) {
		this.row = row;
	}

	//@ ensures \result == col;
	//@ pure
	public Integer getColumn() {
		return col;
	}

	//@ requires col >= 0;
	//@ ensures this.col == row;
	public void setColumn(Integer col) {
		this.col = col;
	}
	
	//@ requires row >= 0;
	//@ requires col >= 0;
	//@ ensures this.row == row;
	//@ ensures this.col == col;
	public void setPositions(int row, int col) {
		this.row = row;	
		this.col = col;
	}
	
	@Override
	public String toString() {
		return row + "/" + col;
	}
}
