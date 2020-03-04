package terms;

public class SimpleTerm extends Term
{
	private int value;

	public SimpleTerm(int value)
	{
		this.value = value;
	}

	public int getValue()
	{
		return value;
	}

	@Override
	public String toString()
	{
		return this.value + "";
	}
}
