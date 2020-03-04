package engine;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import exceptions.InvalidStackFormatException;
import instructions.Cur;
import instructions.Instruction;
import instructions.Quote;
import structures.Code;
import structures.Stack;
import terms.CodedTerm;
import terms.Pair;
import terms.SimpleTerm;
import terms.Term;

public class Engine
{
	private Stack stack;
	private Code code;

	public Engine(Stack stack, Code code)
	{
		this.stack = stack;
		this.code = code;
	}

	public Engine(String str)
	{
		this(new Stack(), new Code(str));
	}

	public Stack runLive() throws IOException
	{
		BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));

		Instruction actuel;
		String entry = "";

		System.out.println("Entrez les codes CAM, puis 'stop' pour arreter");
		
		while (!"stop".equals(entry = reader.readLine()))
		{
			this.code.insert(new Code(entry));
			
			System.out.println(run());
		}

		return this.stack;
	}

	public Stack run()
	{
		System.out.println("Stack\t|\tCode");
		while (!this.code.isEmpty())
		{
			Instruction actuel = this.code.useFirstCode();
			System.out.println(this.stack + "\t|\t" + actuel);

			execute(actuel);
		}

		return this.stack;

	}

	private void execute(Instruction actuel)
	{
		switch (actuel.name())
		{
			case "fst":
				fst();
				break;
			case "snd":
				snd();
				break;
			case "quote":
				Quote quote = (Quote) actuel;
				quote(quote.getValue());
				break;
			case "cur":
				Cur cur = (Cur) actuel;
				cur(cur.getCode());
				break;
			case "push":
				push();
				break;
			case "swap":
				swap();
				break;
			case "cons":
				cons();
				break;
			case "app":
				app();
				break;
			case "plus":
				plus();
				break;
		}
	}

	private void fst()
	{
		if (!this.stack.getFirstTerm().getClass().equals(Pair.class))
		{
			throw new InvalidStackFormatException("(t, t)", this.stack);
		}
		else
		{
			Pair temp = (Pair) this.stack.getFirstTerm();
			this.stack.removeTerm();
			this.stack.insertTerm(temp.getLeft());
		}
	}

	private void snd()
	{
		if (!this.stack.getFirstTerm().getClass().equals(Pair.class))
		{
			throw new InvalidStackFormatException("(t, t)", this.stack);
		}
		else
		{
			Pair temp = (Pair) this.stack.getFirstTerm();
			this.stack.removeTerm();
			this.stack.insertTerm(temp.getRight());
		}
	}

	private void quote(int value)
	{
		SimpleTerm simple = new SimpleTerm(value);
		this.stack.removeTerm();
		this.stack.insertTerm(simple);
	}

	private void cur(Code code)
	{
		Term temp = this.stack.getFirstTerm();

		this.stack.removeTerm();

		this.stack.insertTerm(new CodedTerm(code, temp));
	}

	private void push()
	{
		this.stack.insertTerm(this.stack.getFirstTerm());
	}

	private void swap()
	{
		Term first = this.stack.getFirstTerm();
		Term second = this.stack.getSecondTerm();

		this.stack.removeTerm();
		this.stack.removeTerm();

		this.stack.insertTerm(first);
		this.stack.insertTerm(second);
	}

	private void cons()
	{
		Term first = this.stack.getFirstTerm();
		Term second = this.stack.getSecondTerm();

		this.stack.removeTerm();
		this.stack.removeTerm();

		this.stack.insertTerm(new Pair(second, first));
	}

	private void app()
	{
		Term first = this.stack.getFirstTerm();
		Term second = this.stack.getSecondTerm();

		if (!second.getClass().equals(CodedTerm.class))
		{
			throw new InvalidStackFormatException("t.(C:t)", this.stack);
		}
		else
		{
			CodedTerm coded = (CodedTerm) second;

			this.stack.removeTerm();
			this.stack.removeTerm();

			this.stack.insertTerm(new Pair(coded.getTerm(), first));

			this.code.insert(coded.getCode());
		}
	}

	private void plus()
	{
		Term firstTerm = this.stack.getFirstTerm();
		Term secondTerm = this.stack.getSecondTerm();

		if (!firstTerm.getClass().equals(SimpleTerm.class) || !secondTerm.getClass().equals(SimpleTerm.class))
		{
			throw new InvalidStackFormatException("n.m", this.stack);
		}
		else
		{
			SimpleTerm first = (SimpleTerm) firstTerm;
			SimpleTerm second = (SimpleTerm) secondTerm;

			this.stack.removeTerm();
			this.stack.removeTerm();

			this.stack.insertTerm(new SimpleTerm(first.getValue() + second.getValue()));
		}
	}
}
