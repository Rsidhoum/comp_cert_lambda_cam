package instructions;

import java.util.ArrayList;
import java.util.List;

import exceptions.InvalidInstructionFormatException;
import structures.Code;

public interface Instruction
{
	abstract public String name();

	abstract public String toString();

	public static List<Instruction> toList(String code)
	{
		List<String> names = getSplit(code);

		List<Instruction> list = new ArrayList<Instruction>();

		for (int i = 0; i < names.size(); i++)
		{
			if (names.get(i).contains("cur"))
			{
				if (names.get(i).charAt(0) != '(')
				{
					throw new InvalidInstructionFormatException("paranthesis are missing: (cur C)", names.get(i));
				}
				else
				{
					String newCode = names.get(i).substring(5, findClosingParen(names.get(i)));
					list.add(new Cur(new Code(newCode)));
					System.out.println();
				}

			}
			else if (names.get(i).contains("quote"))
			{
				if (names.get(i).charAt(0) != '(')
				{
					throw new InvalidInstructionFormatException("paranthesis are missing: (quote n)", names.get(i));
				}
				else
				{
					String substring = names.get(i).substring(7, names.get(i).length() - 1);

					try
					{
						int value = Integer.parseInt(substring);
						list.add(new Quote(value));
					}
					catch (NumberFormatException e)
					{
						throw new InvalidInstructionFormatException("'" + substring + "' is not a valid number: (quote n)", names.get(i));
					}
				}
			}
			else
			{
				try
				{
					list.add(EnumInstruction.valueOf(names.get(i)));
				}
				catch (IllegalArgumentException e)
				{
					throw new InvalidInstructionFormatException("it is not a valid CAM instruction", names.get(i));
				}
			}
		}

		return list;
	}

	private static List<String> getSplit(String code)
	{
		List<String> list = new ArrayList<String>();

		while (!"".equals(code))
		{
			int findNextInstruction = findNextInstruction(code);
			list.add(code.substring(0, findNextInstruction));

			if (code.length() != findNextInstruction)
			{
				code = code.substring(findNextInstruction + 1);
			}
			else
			{
				code = "";
			}
		}

		return list;
	}

	private static int findNextInstruction(String code)
	{
		if (code.charAt(0) == '(')
		{
			return findClosingParen(code) + 1;
		}
		else
		{
			int index = 0;

			while (index < code.length() && code.charAt(index) != ';')
			{
				index++;
			}

			return index;
		}
	}

	private static int findClosingParen(String text)
	{
		int closePos = 0;
		int counter = 1;

		while (counter > 0)
		{
			char c = text.charAt(++closePos);

			if (c == '(')
			{
				counter++;
			}
			else if (c == ')')
			{
				counter--;
			}
		}

		return closePos;
	}
}