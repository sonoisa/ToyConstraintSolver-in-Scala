object Example extends FiniteDomainConstraintSolver {
	import monad._
	import dsl._
	
	/**
	 * 練習問題 1
	 * 
	 * 制約条件
	 * x は 0 〜 3 である。
	 * y は 0 〜 3 である。
	 * x < y または x = y である。
	 * x = 2 である。
	 * 
	 * 解答
	 * (x, y) = (2, 2), (2, 3)
	 */
	def test1 = {
		val problem = for {
			x <- newVar(0 to 3)
			y <- newVar(0 to 3)
			_ <- (x < y) || (x === y)
			_ <- x === 2
			solution <- labeling(Stream(x, y))
		} yield solution
		solve(problem) foreach { solution => 
			println(solution.zip(List("x: ", "y: ")) map { case (s, l) => l + s } mkString(", "))
		}
	}
	
	/**
	 * 練習問題 2
	 * 
	 * 問題
	 * 次の数独を解く。
	 *  , , , ,8, , , , 
	 *  , , ,1, ,6,5, ,7
	 * 4, ,2,7, , , , , 
	 *  ,8, ,3, , ,1, , 
	 *  , ,3, , , ,8, , 
	 *  , ,5, , ,9, ,7, 
	 *  ,5, , , ,8, , ,6
	 * 3, ,1,2, ,4, , , 
	 *  , ,6, ,1, , , , 
	 * 
	 * 解答
	 * 5,6,7,4,8,3,2,9,1
	 * 9,3,8,1,2,6,5,4,7
	 * 4,1,2,7,9,5,3,6,8
	 * 6,8,9,3,7,2,1,5,4
	 * 7,4,3,6,5,1,8,2,9
	 * 1,2,5,8,4,9,6,7,3
	 * 2,5,4,9,3,8,7,1,6
	 * 3,7,1,2,6,4,9,8,5
	 * 8,9,6,5,1,7,4,3,2
	 */
	def test2 = {
		type Puzzle = Stream[Int]
		val table: Puzzle = Stream(
			0, 0, 0, 0, 8, 0, 0, 0, 0,
			0, 0, 0, 1, 0, 6, 5, 0, 7,
			4, 0, 2, 7, 0, 0, 0, 0, 0,
			0, 8, 0, 3, 0, 0, 1, 0, 0,
			0, 0, 3, 0, 0, 0, 8, 0, 0,
			0, 0, 5, 0, 0, 9, 0, 7, 0,
			0, 5, 0, 0, 0, 8, 0, 0, 6,
			3, 0, 1, 2, 0, 4, 0, 0, 0,
			0, 0, 6, 0, 1, 0, 0, 0, 0)
		
		def chunk[A](n: Int): Stream[A] => Stream[Stream[A]] = {
			case Stream.Empty => Stream.Empty
			case xs => {
				val (ys, zs) = xs.splitAt(n)
				Stream.cons(ys, chunk(n)(zs))
			}
		}
		def show(p: Puzzle): String = chunk(9)(p) map { _.map { x => if (x == 0) " " else x.toString } mkString("", ",", "\n") } mkString("")
		def rows[A]: Stream[A] => Stream[Stream[A]] = chunk(9)
		def columns[A]: Stream[A] => Stream[Stream[A]] = chunk(9)(_).transpose
		def boxes[A]: Stream[A] => Stream[Stream[A]] = { p => chunk(3)(chunk(3)(chunk(3)(p))).map { _.transpose.map { _.flatten } }.flatten }
		
		def sudoku(puzzle: Puzzle) = {
			for {
				vars <- newVars(81, 1 to 9 toList)
				_ <- zipWithM(vars)(puzzle)(x => n => when (n > 0) { hasValue(x, n) })
				_ <- mapM(rows(vars)) { allDifferent }
				_ <- mapM(columns(vars)) { allDifferent }
				_ <- mapM(boxes(vars)) { allDifferent }
				solution <- labeling(vars)
			} yield solution
		}
		val problem = sudoku(table)
		
		println("problem")
		println(show(table))
		println("solution")
		var beginTime = System.nanoTime
		solve(problem).take(1) foreach { solution => println(show(solution)) }
		println("時間: " + (System.nanoTime - beginTime) / 1000000000.0 + "sec") 
	}
	
	/**
	 * 練習問題 3
	 * 
	 * 問題
	 * 3 x 3 の魔法陣を解く。
	 * 
	 * 解答
	 * 6,1,8
	 * 7,5,3
	 * 2,9,4
	 * 
	 * 6,7,2
	 * 1,5,9
	 * 8,3,4
	 * 
	 * 2,9,4
	 * 7,5,3
	 * 6,1,8
	 * 
	 * 2,7,6
	 * 9,5,1
	 * 4,3,8
	 * 
	 * 8,1,6
	 * 3,5,7
	 * 4,9,2
	 * 
	 * 8,3,4
	 * 1,5,9
	 * 6,7,2
	 * 
	 * 4,9,2
	 * 3,5,7
	 * 8,1,6
	 * 
	 * 4,3,8
	 * 9,5,1
	 * 2,7,6
	 */
	def test3 = {
		def chunk[A](n: Int): Stream[A] => Stream[Stream[A]] = {
			case Stream.Empty => Stream.Empty
			case xs => {
				val (ys, zs) = xs.splitAt(n)
				Stream.cons(ys, chunk(n)(zs))
			}
		}
		def show[A](p: Stream[A]): String = chunk(3)(p) map { _.mkString("", ",", "\n") } mkString("")
		def rows[A]: Stream[A] => Stream[Stream[A]] = chunk(3)
		def columns[A]: Stream[A] => Stream[Stream[A]] = chunk(3)(_).transpose
		def diagonals[A]: Stream[A] => Stream[Stream[A]] = { p => Stream(Stream(p(0), p(4), p(8)), Stream(p(2), p(4), p(6))) }
		
		val magicTable = {
			for {
				vars <- newVars(9, 1 to 9)
				s <- newVar((1 + 2 + 3) to (7 + 8 + 9))
				_ <- allDifferent(vars)
				_ <- mapM(rows(vars)) { allDifferent }
				_ <- mapM(columns(vars)) { allDifferent }
				_ <- mapM(diagonals(vars)) { allDifferent }
				_ <- mapM(rows(vars)) { row => equalToSumOf(s)(row) }
				_ <- mapM(columns(vars)) { col => equalToSumOf(s)(col) }
				_ <- mapM(diagonals(vars)) { diag => equalToSumOf(s)(diag) }
				solution <- labeling(vars)
			} yield solution
		}
		
		var beginTime = System.nanoTime
		solve(magicTable).take(1) foreach { solution =>println(show(solution)) }
		println("時間: " + (System.nanoTime - beginTime) / 1000000000.0 + "sec") 
	}
	
	/**
	 * 練習問題 4
	 * 
	 * 問題
	 * SEND + MORE = MONEY を解く。
	 * 
	 * 解答
	 * 9567 + 1085 = 10652
	 */
	def test4 = {
		val sendMoreMoney = {
			for {
				vars <- newVars(8, 0 to 9)
				val Stream(s, e, n, d, m, o, r, y) = vars
				_ <- s !== 0
				_ <- m !== 0
				_ <- allDifferent(vars)
//				send <- newVar(1023 to 9876)
//				more <- newVar(1023 to 9876)
//				money <- newVar(10234 to 98765)
//				_ <- equalToAddOf(money)(send, more)
//				_ <- send === 1000 * s + 100 * e + 10 * n + d
//				_ <- more === 1000 * m + 100 * o + 10 * r + e
//				_ <- money === 10000 * m + 1000 * o + 100 * n + 10 * e + y
				_ <- (1000 * (s + m) + 100 * (e + o) + 10 * (n + r) + d + e) === (10000 * m + 1000 * o + 100 * n + 10 * e + y)
//				_ <- (1000 * s + 100 * e + 10 * n + d + 1000 * m + 100 * o + 10 * r + e) === (10000 * m + 1000 * o + 100 * n + 10 * e + y)
				solution <- labeling(Stream(s, e, n, d, m, o, r, e, m, o, n, e, y))
			} yield solution
		}
		
		var beginTime = System.nanoTime
		solve(sendMoreMoney).take(1) foreach { solution =>println(solution.mkString(", ")) }
		println("時間: " + (System.nanoTime - beginTime) / 1000000000.0 + "sec") 
	}
	
	def main(args: Array[String]): Unit = {
		test1
		test2
		test3
		test4
	}
}
