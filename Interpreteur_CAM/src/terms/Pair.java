package terms;

public class Pair extends Term
{
	private Term left;
	private Term right;
	
	public Pair(Term left, Term right)
	{
		this.left = left;
		this.right = right;
	}

	public Term getLeft()
	{
		return this.left;
	}

	public Term getRight()
	{
		return this.right;
	}

	@Override
	public String toString()
	{
		return "(" + this.left + ", " + this.right + ")";
	}
	
}
