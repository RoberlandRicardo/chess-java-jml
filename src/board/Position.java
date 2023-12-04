package board;

public class Position {

	private Integer row;
	private Integer col;
	
	//@ pure
	public Position (int row, int col) {
		this.row = row;
		this.col = col;
	}

	//@ pure
	public Integer getRow() {
		return row;
	}

	public void setRow(Integer row) {
		this.row = row;
	}

	//@ pure
	public Integer getColumn() {
		return col;
	}

	public void setColumn(Integer col) {
		this.col = col;
	}
	
	public void setPositions(int row, int col) {
		this.row = row;
		this.col = col;
	}
	
	@Override
	public String toString() {
		return row + "/" + col;
	}
}
