--Rain Rähni, Project Sudoku.
import Data.List
import Data.Maybe
import Data.Vect
import Data.Nat
import Data.Fin
import System.File
import Data.String


--Task 1
--Im creating a sudoku table that is a Vector with length 9 of Vectors with length 9 and in each Vector there are Maybe Nats. 
-- Just Nat represents a number in a cell and Nothing represents an empty cell.
data SudokuTable : Type where
  MkSudokuTablePartial : Vect 9 (Vect 9 (Maybe Nat)) -> SudokuTable

partiallyFilledTable : SudokuTable
partiallyFilledTable = MkSudokuTablePartial [
    [Just 5, Just 3, Nothing, Nothing, Just 7, Nothing, Nothing, Nothing, Nothing],
    [Just 6, Nothing, Nothing, Just 1, Just 9, Just 5, Nothing, Nothing, Nothing],
    [Nothing, Just 9, Just 8, Nothing, Nothing, Nothing, Nothing, Just 6, Nothing],
    [Just 8, Nothing, Nothing, Nothing, Just 6, Nothing, Nothing, Nothing, Just 3],
    [Just 4, Nothing, Nothing, Just 8, Nothing, Just 3, Nothing, Nothing, Just 1],
    [Just 7, Nothing, Nothing, Nothing, Just 2, Nothing, Nothing, Nothing, Just 6],
    [Nothing, Just 6, Nothing, Nothing, Nothing, Nothing, Just 2, Just 8, Nothing],
    [Nothing, Nothing, Nothing, Just 4, Just 1, Just 9, Nothing, Nothing, Just 5],
    [Nothing, Nothing, Nothing, Nothing, Just 8, Nothing, Nothing, Just 7, Just 9]
  ]

partiallyFilledTableThree : SudokuTable
partiallyFilledTableThree = MkSudokuTablePartial [
  [Nothing, Just 2, Just 3, Just 4, Nothing, Just 6, Just 7, Just 8, Just 9],
  [Just 4, Just 5, Nothing, Nothing, Just 8, Just 9, Nothing, Just 2, Just 3],
  [Just 7, Just 8, Just 9, Just 1, Just 2, Just 3, Just 4, Just 5, Just 6],
  [Just 2, Nothing, Just 4, Nothing, Nothing, Just 5, Just 8, Just 9, Just 7],
  [Just 3, Just 6, Nothing, Nothing, Just 9, Nothing, Nothing, Just 1, Just 4],
  [Nothing, Just 9, Nothing, Just 2, Just 1, Just 4, Just 3, Nothing, Just 5],
  [Nothing, Just 3, Just 1, Just 6, Just 4, Nothing, Nothing, Nothing, Just 8],
  [Just 6, Nothing, Nothing, Just 9, Just 7, Just 8, Just 5, Just 3, Just 1],
  [Just 9, Just 7, Just 8, Nothing, Nothing, Just 1, Just 6, Nothing, Just 2]
]


--Task 2
--1) First 2 functions are defined from lectures or labs. Index function.
forget_length : Vect n a -> List a
forget_length [] = []
forget_length (x :: xs) = x :: forget_length xs

index_list : Nat -> List a -> Maybe a
index_list k [] = Nothing
index_list Z (x :: xs) = Just x
index_list (S k) (x :: xs) = index_list k xs

index : (s : SudokuTable) -> (i : Nat) -> (j : Nat) -> Maybe Nat
index (MkSudokuTablePartial rows) i j =
--with index list we get element from rows
  case index_list i (forget_length rows) of
  --if i out of bounds
    Nothing => Just 10
    -- if i within the bounds
    Just cells =>
    --with index list we get element from cells
      case index_list j (forget_length cells) of
        Nothing => Just 10
        Just cell => cell
--2) 
learn_length : (xs : List a) -> Vect (length xs) a
learn_length [] = []
learn_length (x :: xs) = x :: learn_length xs

-- i defined replaceAt function.
--return a vector where element at position i has been replaced with x
replaceAt1 : (i : Fin n) -> (x : a) -> (xs : Vect n a) -> Vect n a
replaceAt1 FZ x (_ :: xs) = x :: xs
replaceAt1 (FS i) x (y :: xs) = y :: replaceAt1 i x xs

update : (s : SudokuTable) -> (i : Fin 9) -> (j : Fin 9) -> (n : Nat) -> SudokuTable
update (MkSudokuTablePartial rows) i j n =
  let
  --newRows will be updated row, gets a row at index i, replaces element at j with element n and then replaces the row at i index
  --with updated row.  
    newRow = replaceAt i (replaceAt j (Just n) (index i rows)) rows
  in
    MkSudokuTablePartial newRow

--3) I define countEmptyCells that uses map to apply the count function to each row of the table. it counts the number of cells
--that are "Nothing" in a row.

countEmptyCells : (s : SudokuTable) -> Nat
countEmptyCells (MkSudokuTablePartial rows) =
  let
    rowEmptyCells : Vect 9 Nat
    rowEmptyCells = map (\row => count (\cell => isNothing cell) row) rows
  in
    sum rowEmptyCells

-- calculate difficulty of the table, get total amount of empty cells and divide total amount of cells (81) fromInteger 
--converts empty cell count to a double.
difficulty : (s : SudokuTable) -> Double
difficulty s =
  let
    emptyCells = countEmptyCells s
    totalCells = 9.0 * 9.0
  in
    fromInteger (natToInteger emptyCells) / totalCells

--4)

--splits list into sublists with size of n
chunksOf : Nat -> List a -> List (List a)
chunksOf n [] = []
--splits list into first n elements, appends it to recursively splitting elements to chunks of size n
chunksOf n xs = take n xs :: chunksOf n (drop n xs)

--checks whether all elements in list are unique, nub removes duplicates from the list.
allUnique : List Nat -> Bool
allUnique xs = nub xs == xs

--converts vect of vects to list of lists (to sudoku grid.)
toBlocks : Vect 9 (Vect 9 (Maybe Nat)) -> List (List (Maybe Nat))
toBlocks table =
  let
  --maps over each row converting it to list and splits it to sublists of szize 3
    chunksOf3 = map (chunksOf 3 . toList) (toList table)
    --concats all these sublists, im transposing it so that each inner list contains elements from original columns
    rowsOfBlocks = concat $ map transpose chunksOf3
  in
    map concat $ chunksOf 3 rowsOfBlocks

--Checks whether solution/table is correct by checking uniqueness in rows, columns and blocks
isValid : SudokuTable -> Bool
isValid (MkSudokuTablePartial table) =
  let
    rows = toList table
    cols = toList $ transpose table
    blocks = toBlocks table
  in
    --every line converts row,column or block to list, removes Nothing values (with catMaybes) and check if lists are unique.
    all (allUnique . catMaybes . toList) rows &&
    all (allUnique . catMaybes . toList) cols &&
    all (allUnique . catMaybes) blocks
    
--5)
--Returns true if sudoku table is valid and contains no Nothing values.
isComplete : SudokuTable -> Bool
isComplete (MkSudokuTablePartial table) =
--checks whether table is valid, checks if all elements in list that is created in parentheses are Just elements.
  isValid (MkSudokuTablePartial table) && all isJust (concat $ toList $ map toList table)

--task3
--parses string to maybe nat. "." is empty cell and returns Nothing, else are numbers.
parseCell : String -> Maybe Nat
parseCell "." = Nothing
parseCell x = Just (cast x)

--tries to convert list of elements into vector of 9 with these elements.
fromList9 : List a -> Maybe (Vect 9 a)
fromList9 [a, b, c, d, e, f, g, h, i] = Just [a, b, c, d, e, f, g, h, i]
--any other input list (that does not contain 9 exactly 9 elements)
fromList9 _ = Nothing


parseRow : String -> Either String (Vect 9 (Maybe Nat))
parseRow row =
--word row splits input row to list of elements and parcecell converts each element to Maybe Nat
    case fromList9 (map parseCell (words row)) of
      --Just cells indicate correct converting with fromList9
        Just cells => Right cells
        Nothing => Left "Invalid row: must contain exactly 9 cells"

--parsing it into SudokuTable if possible.
parseTable : String -> Either String SudokuTable
parseTable input =
    --splits input string into lines.
    let rows = map parseRow (lines input) in
    --traverse combines Either values into an individual Either value.
    case traverse id rows of
        --if any of the rows contains an error
        Left err => Left err
        --if all rows are valud
        Right rows =>
            case fromList9 rows of
                --If converting was successful parsing was successful
                Just vrows => Right (MkSudokuTablePartial vrows)
                --input table is invalid.
                Nothing => Left "Invalid table: must contain exactly 9 rows"

--Reads sudoku table from the file
readSudokuFile : String -> IO (Either String SudokuTable)
readSudokuFile filename = do
    --binds the contents from filename to result.
    result <- readFile filename
    case result of
        --if an error occurred when reading the file
        Left err => pure (Left (show err))
        --if redaing from file was successful
        Right contents => pure (parseTable contents)


--To represent table.
Show SudokuTable where
    show (MkSudokuTablePartial table) = "MkSudokuTablePartial " ++ show (toList (map toList table))


--Following main function was used for testing if parsing works.
-- main : IO ()
-- main = do
--     result <- readSudokuFile "parserTest.txt"
--     case result of
--         Left err => putStrLn err
--         Right table => putStrLn (show table)
  
--task4

prettyPrint : SudokuTable -> IO ()
prettyPrint (MkSudokuTablePartial table) = do
    --Top border of table
    putStrLn "+ - - - + - - - + - - - +"
    --print rows of the table
    printRows table
    --Footer of the table.
    putStrLn "+ - - - + - - - + - - - +"
  where
    --applies f to each element of the vector and performas IO action for each.
    mapM_ : (a -> IO ()) -> Vect n a -> IO ()
    mapM_ f [] = pure ()
    mapM_ f (x :: xs) = do
        f x
        mapM_ f xs
      --prints single cell of the table
    printCell : Maybe Nat -> IO ()
    printCell (Just n) = do
        putStr (show n ++ " ")
    printCell Nothing = do
        putStr "  "
     -- prints row 
    printRow : Vect 9 (Maybe Nat) -> IO ()
    printRow row = do
      putStr "| "
      mapM_ printCell (take 3 row)
      putStr "| "
      mapM_ printCell (take 3 (drop 3 row))
      putStr "| "
      mapM_ printCell (drop 6 row)
      putStrLn "|"
      --prints multiple rows
    printRows : Vect 9 (Vect 9 (Maybe Nat)) -> IO ()
    printRows rows = do
        mapM_ printRow (take 3 rows)
        putStrLn "+ - - - + - - - + - - - +"
        mapM_ printRow (take 3 (drop 3 rows))
        putStrLn "+ - - - + - - - + - - - +"
        mapM_ printRow (drop 6 rows)

--Following main function was used for testing if pretty printing works.
-- main : IO ()
-- main = prettyPrint partiallyFilledTable

--task5
--Parse input string to Nat
parse : String -> Nat
parse str = case parseInteger str of
              --if parsing failed
              Nothing => 0
              --integer to nat
              Just x => cast x

--Function that lets us play.
gameLoop : SudokuTable -> IO ()
gameLoop table =
  do
    putStrLn "Current grid:"
    --Pretty prints current table
    prettyPrint table
    --If complete
    if isComplete table
      then putStrLn "Congratulations, the grid is now solved."
      --if not
      else do
        putStrLn "Enter (i, j) coordinates:"
        i <- getLine
        j <- getLine
        --if either of the coordinates or not entered.
        if i == "" || j == ""
          then do
            putStrLn "Invalid coordinates. Enter another pair of coordinates:"
            --continue game
            gameLoop table
          --if cooordinates entered, convert entered nats into fins
          else case (natToFin (parse i) 9, natToFin (parse j) 9) of
            (Just i', Just j') => do
              putStrLn "Enter the number to fill the cell:"
              n <- getLine
              --if no number entered (a fix if player just presses enter)
              if n == ""
                then do
                  putStrLn "Invalid number. Enter another number:"
                  gameLoop table
                else let n' = parse n in
                  -- update the cell at entered coordinates.
                  let newTable = update table i' j' n' in
                  if isValid newTable
                    then gameLoop newTable
                    -- if entered number is illegal
                    else do
                      putStrLn "Impossible to fill the cell with that number. Enter another number:"
                      gameLoop table
            _ => do
            --if coordinates out of bounds
              putStrLn "Invalid coordinates. Enter another pair of coordinates:"
              gameLoop table

main : IO ()
main = gameLoop partiallyFilledTable

--task6
--Find first hole in sudokutable.
findHole : (s : SudokuTable) -> Maybe (Fin 9, Fin 9)
findHole s =
  let
    --helper function search
    search : (i : Fin 9) -> (j : Fin 9) -> Maybe (Fin 9, Fin 9)
    search i j =
    if j == 8
      then do
      --move search to the next row
      search (i + 1) 0
      else if isNothing (index s (finToNat i) (finToNat j))
        --if isnothing then we have found the hole
        then Just (i, j)
        else do
        --move the search to next column in same row.
          search i (j + 1)

  in
    --start a search for a hole
    search 0 0

--task7
solve : (s : SudokuTable) -> List SudokuTable
solve s =
  if not (isValid s) then [] -- if not valid, no solution
  else if isComplete s then [s] -- if valid but alredy complete, only one solution
  else let
    (i, j) = fromMaybe (0,0) (findHole s) -- get the first hole, if findhole returns Nothing then 0,0 is used as default.
    possibleDigitsList = filter (\n => isValid (update s i j n)) [1,2,3,4,5,6,7,8,9] -- checks if table is valid if some number would be placed
                                                                                    -- at given hole
    --places each n at i j from possibleDigits
    in concatMap (\n => solve (update s i j n)) possibleDigitsList
