package main;

import java.io.IOException;

import engine.Engine;

public class Main
{

	public static void main(String[] args)
	{
		Engine eng;// = new Engine("");
		
		/*try
		{
			System.out.println(eng.runLive());
		}
		catch (IOException e)
		{
			e.printStackTrace();
		}*/
		
		eng = new Engine("(quote 4);push;(cur push;fst;swap;snd;plus;push);swap;(quote 5);push;plus;app;plus");
		System.out.println(eng.run());
	}

}
