package exceptions;

@SuppressWarnings("serial")
public class InvalidInstructionFormatException extends RuntimeException
{
	public InvalidInstructionFormatException(String correctFormat, String wrongString) {
		super("Format is invalid, found '" + wrongString + "', but " + correctFormat);
	}
}
