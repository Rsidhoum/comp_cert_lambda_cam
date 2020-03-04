package instructions;

import structures.Code;

public class Cur implements Instruction
{
	private Code code;

	public Cur(Code code)
	{
		this.code = code;
	}

	public Code getCode()
	{
		return code;
	}

	@Override
	public String name()
	{
		return "cur";
	}

	public String toString()
	{
		return "(" + name() + " " + getCode() + ")";
	}
}
