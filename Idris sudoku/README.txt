No dependencies are required.

Prerequisites:

Have IDE open in ubuntu. (I have windows therefore i downloaded and connect to WSL:ubuntu in vscode)
To play the game yourself in repl you need to do the following:
1. Go to correct directory in terminal
2. type idris2 Game.idr 
3. In repl type :exec main
4. Now you should be able to play the game :)


In Game.idr is the fully documented code, also it`s main function allows to play the game.
parserTest.txt is a sample input file that contains partially filled Sudoku table
TestSolve.idr`s main function read input file, pretty print`s the solution(s) to the terminal.
