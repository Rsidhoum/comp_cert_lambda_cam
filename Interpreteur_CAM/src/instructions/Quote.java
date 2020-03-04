package instructions;

public class Quote implements Instruction
{
	private int value;

	public Quote(int value)
	{
		this.value = value;
	}

	public int getValue()
	{
		return this.value;
	}

	@Override
	public String name()
	{
		return "quote";
	}

	public String toString()
	{
		return "(" + name() + " " + getValue() + ")";
	}
}
