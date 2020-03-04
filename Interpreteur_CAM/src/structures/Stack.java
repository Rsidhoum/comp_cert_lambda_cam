package structures;

import java.util.ArrayList;
import java.util.List;

import exceptions.InvalidStackFormatException;
import terms.EmptyTerm;
import terms.Term;

public class Stack
{

	private List<Term> stack;

	public Stack()
	{
		this.stack = new ArrayList<Term>();
		insertTerm(new EmptyTerm());
	}

	public void insertTerm(Term toInsert)
	{
		this.stack.add(0, toInsert);
	}

	public Term removeTerm() throws InvalidStackFormatException
	{
		if (this.stack.size() == 0)
		{
			String error = "t";

			throw new InvalidStackFormatException(error, this);
		}
		else
		{
			return this.stack.remove(0);
		}
	}

	public Term getFirstTerm() throws InvalidStackFormatException
	{
		return getTerm(0);
	}

	public Term getSecondTerm() throws InvalidStackFormatException
	{
		return getTerm(1);
	}

	private Term getTerm(int index) throws InvalidStackFormatException
	{
		if (this.stack.size() <= index)
		{
			String error = "t";

			for (int i = 1; i <= index; i++)
			{
				error += ".t";
			}

			throw new InvalidStackFormatException(error, this);
		}
		else
		{
			return this.stack.get(index);
		}
	}
	
	public String toString() {
		String s = "";
		
		for (int i = 0; i < this.stack.size(); i++) {
			s += this.stack.get(i).toString();
			
			if (i != this.stack.size() - 1) {
				s += ".";
			}
		}
		
		return s;
	}
}
