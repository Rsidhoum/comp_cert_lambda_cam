package exceptions;

import structures.Stack;

@SuppressWarnings("serial")
public class InvalidStackFormatException extends RuntimeException
{
	public InvalidStackFormatException(String correctFormat, Stack wrongStack) {
		super("Format is invalid, should be '" + correctFormat + "', but is " + wrongStack);
	}
}
