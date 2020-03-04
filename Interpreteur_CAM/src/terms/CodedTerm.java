package terms;

import structures.Code;

public class CodedTerm extends Term
{
	private Code code;
	private Term term;
	
	public CodedTerm(Code code, Term term)
	{
		this.code = code;
		this.term = term;
	}

	public Code getCode()
	{
		return code;
	}

	public Term getTerm()
	{
		return term;
	}

	@Override
	public String toString()
	{
		return "(" + this.code + ":" + this.term + ")";
	}
}
