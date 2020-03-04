package structures;

import java.util.ArrayList;
import java.util.List;

import instructions.Instruction;

public class Code
{
	private List<Instruction> code;

	public Code()
	{
		this.code = new ArrayList<Instruction>();
	}

	public Code(String code)
	{
		this();
		this.code.addAll(Instruction.toList(code));
	}

	public void insert(Code code)
	{
		this.code.addAll(0, code.code);
	}

	public Instruction useFirstCode()
	{
		return this.code.remove(0);
	}

	public boolean isEmpty()
	{
		return this.code.isEmpty();
	}
	
	public String toString() {
		String s = "";
		
		for (int i = 0; i < this.code.size(); i++) {
			s += this.code.get(i).toString();
			
			if (i != this.code.size() - 1) {
				s += ";";
			}
		}
		
		return s;
	}
}
