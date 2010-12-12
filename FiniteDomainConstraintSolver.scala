/**
 * Toy Finite Domain Constraint Solver
 * 
 * http://overtond.blogspot.com/2008/07/pre.html に下記の拡張を追加したもの
 * 
 * 1. 算術演算を行えるようにした。
 * 2. 探索戦略を動的変数順序ヒューリスティクスにした。
 * 3. 領域の実装として集合と範囲が使えるようにした。
 */
trait FiniteDomainConstraintSolver {
	/** 制約充足解探索モナド (探索開始時の状態 => (制約充足解, 発見時の状態) の遅延リスト) */
	case class FD[A](run: State => Stream[(A, State)]) {
		def flatMap[B](k: A => FD[B]): FD[B] = FD(s0 => run(s0) flatMap { case (a, s1) => k(a).run(s1) })
		def map[B](f: A => B): FD[B] = FD(s0 => run(s0) map { case (a, s1) => (f(a), s1) })
	}
	
	/** 制約充足解探索モナドの基本関数とアクション */
	class FDMonad {
		type M[A] = FD[A]
		
		// Moand
		val unit0: M[Unit] = unit(())
		def unit[A](a: A): M[A] = FD(s => Stream((a, s)))
		def bind[A, B](m: M[A])(k: A => M[B]): M[B] = m flatMap k
		def sequence[A](ms: Stream[M[A]]): M[Stream[A]] = {
			def k(m: M[A], m2: M[Stream[A]]): M[Stream[A]] = {
				m flatMap { x => m2 flatMap { xs => unit(x #:: xs) }}
			}
			ms.foldRight[M[Stream[A]]](unit(Stream.Empty))(k)
		}
		def mapM[A, B](as: Stream[A])(k: A => M[B]): M[Stream[B]] = sequence(as map { a => k(a) })
		def replicateM[A](n: Int)(m: M[A]): M[Stream[A]] = sequence(Stream.fill(n)(m))
		def zipWithM[A, B, C](xs: Stream[A])(ys: Stream[B])(f: A => B => M[C]): M[Stream[C]] = sequence(zipWith(xs)(ys)(f))
		def zipWith[A, B, C](xs: Stream[A])(ys: Stream[B])(f: A => B => M[C]): Stream[M[C]] = (xs, ys) match {
			case (x #:: xs, y #:: ys) => Stream.cons(f(x)(y), zipWith(xs)(ys)(f))
			case _ => Stream.Empty
		}
		def when(p: Boolean)(m: => M[Unit]): M[Unit] = if (p) m else unit0
		
		// MonadPlus
		def mzero[A](): M[A] = FD(_ => Stream.Empty)
		def mplus[A](lhs: M[A], rhs: M[A]): M[A] = FD(s => lhs.run(s) #::: rhs.run(s))
		private val mzero0 = mzero[Unit]
		def guard(p: Boolean): M[Unit] = if (p) unit0 else mzero0
		
		// MonadTrans
		def lift[A](m: Stream[A]): M[A] = FD(s => m map { a => (a, s) })
		
		// MonadList
		def concat[A](ms: Stream[M[A]]): M[A] = FD(s => ms map { _.run(s) } flatten)
		
		// MonadState
		def get(): M[State] = FD(s => Stream.cons((s, s), Stream.Empty))
		def put(s: State): M[Unit] = FD(_ => Stream(((), s)))
		def modify(f: State => State): M[Unit] = get flatMap { s => put(f(s)) }
	}
	
	val monad = new FDMonad
	import monad._
	
	/** 有限領域 */
	sealed trait Domain {
		def contains(value: Int): Boolean
		def size: Int
		def -(value: Int): Domain
		def --(that: Domain): Domain
		def isEmpty: Boolean
		def &(that: Domain): Domain
		def subsetOf(that: Domain): Boolean
		def toStream: Stream[Int]
		def min: Int
		def max: Int
		def filter(p: Int => Boolean): Domain
		def map(f: Int => Int): Domain
		def foreach(f: Int => Unit): Unit
	}
	
	final case class SetDomain(values: Set[Int]) extends Domain {
		def contains(value: Int): Boolean = values.contains(value)
		def size: Int = values.size
		def -(value: Int): Domain = new SetDomain(values - value)
		def --(that: Domain): Domain = that match {
			case SetDomain(s) => new SetDomain(values -- s)
			case RangeDomain(s, e) => new SetDomain(values.filter(value => (s > value || value > e)))
		}
		def isEmpty: Boolean = values.isEmpty
		def &(that: Domain): Domain = that match {
			case SetDomain(s) => new SetDomain(values & s)
			case RangeDomain(s, e) => new SetDomain(values.filter(value => (s <= value && value <= e)))
		}
		def subsetOf(that: Domain): Boolean = that match {
			case SetDomain(s) => values.subsetOf(s)
			case RangeDomain(s, e) => {
				val min = values.min
				val max = values.max
				(s <= min && max <= e)
			}
		}
		def toStream: Stream[Int] = values.toStream
		def min: Int = values.min
		def max: Int = values.max
		def filter(p: Int => Boolean): Domain = new SetDomain(values.filter(p))
		def map(f: Int => Int): Domain = new SetDomain(values map f)
		def foreach(f: Int => Unit): Unit = values foreach f
		override def equals(other: Any): Boolean = {
			other match {
				case SetDomain(s) => values == s
				case that: RangeDomain => subsetOf(that) && that.subsetOf(this)
				case _ => false
			}
		}
		override def hashCode: Int = values.hashCode
	}
	
	final case class RangeDomain(start: Int, end: Int) extends Domain {
		def contains(value: Int): Boolean = (start <= value && value <= end)
		def size: Int = (end - start + 1)
		def -(value: Int): Domain = {
			if (value == start) {
				if (start < end) new RangeDomain(start + 1, end) else EmptyDomain
			} else if (value == end) {
				if (start < end) new RangeDomain(start, end - 1) else EmptyDomain
			} else if (start < value && value < end) {
				new SetDomain((start to value - 1).toSet | (value + 1 to end).toSet)
			} else {
				this
			}
		}
		def --(that: Domain): Domain = that match {
			case SetDomain(s) => {
				if (s.min > end || s.max < start) {
					this
				} else {
					new SetDomain((for { i <- start to end; if (!s.contains(i)) } yield i) toSet)
				}
			}
			case RangeDomain(s, e) => {
				if (s > end || e < start) {
					this
				} else if (start < s && e < end) { // s <= end && e >= start
					new SetDomain((start to s).toSet | (e to end).toSet)
				} else if (start < s) { // s <= end && e >= start && (start >= s || e >= end)
					new RangeDomain(start, s - 1)
				} else if (e < end) { // s <= end && e >= start && start >= s
					new RangeDomain(e + 1, end)
				} else { // s <= end && e >= start && start >= s && e >= end
					EmptyDomain
				}
			}
		}
		def isEmpty: Boolean = (start > end)
		def &(that: Domain): Domain = that match {
			case SetDomain(s) => new SetDomain(s.filter(value => (start <= value && value <= end)))
			case RangeDomain(s, e) => new RangeDomain(start.max(s), end.min(e))
		}
		def subsetOf(that: Domain): Boolean = that match {
			case SetDomain(s) => s.forall(value => (start <= value && value <= end))
			case RangeDomain(s, e) => (s <= start && end <= e)
		}
		def toStream: Stream[Int] = (start to end) toStream
		val min: Int = start
		val max: Int = end
		def filter(p: Int => Boolean): Domain = new SetDomain((start to end) filter p toSet)
		def map(f: Int => Int): Domain = new SetDomain((start to end) map f toSet)
		def foreach(f: Int => Unit): Unit = for (i <- start to end) { f }
		override def equals(other: Any): Boolean = {
			other match {
				case that: SetDomain => subsetOf(that) && that.subsetOf(this)
				case RangeDomain(s, e) => (s == start && e == end)
				case _ => false
			}
		}
		override def hashCode: Int = { start + 41 * (end + 41) }
	}
	
	val EmptyDomain = SetDomain(Set.empty)
	
	object Domain {
		def apply(values: Set[Int]): Domain =  new SetDomain(values)
		def apply(value: Int): Domain = new SetDomain(Set(value))
		def apply(start: Int, end: Int): Domain = new RangeDomain(start, end)
	}
	
	/** 整数領域の最小値 */
	val minDomainValue = -100
	
	/** 整数領域の最大値 */
	val maxDomainValue = 100
	
	/** 整数領域全体 */
	val allDomainValue: Domain = Domain(minDomainValue, maxDomainValue)
	
	/** 制約 */
	type Constraint = FD[Unit]
	
	/** 変数 */
	case class Var(index: Int)
	
	/** 変数に課された制約と取りうる値 */
	case class VarInfo(delayedConstraints: Constraint, countOfConstraints: Int, values: Domain)
	
	/** 変数環境 */
	type VarMap = Map[Var, VarInfo]
	
	/** 解の探索状態 (次に割当可能な変数、変数環境、値が決まっていない変数、制約ネットワーク) */
	case class State(varSupply: Var, varMap: VarMap, indefiniteVars: Set[Var] /* , network: List[String] */)
	
	/** 制約充足解を探す。 */
	def solve[A](fd: FD[A]): Stream[A] = fd.run(initState).map(_._1)
	
	/** 初期状態 */
	val initState: State = State(Var(0), Map.empty, Set.empty /* , Nil */)
	
	/** 領域が domain である新規変数を返す。 */
	def newVar(domain: Domain): FD[Var] = {
		val nextVar: FD[Var] = for {
				state <- get
				val x = state.varSupply
				_ <- put(state.copy(varSupply = Var(x.index + 1)))
			} yield x
		def isOneOf(x: Var, domain: Domain): Constraint = modify(state => {
				val env = state.varMap
				val info = VarInfo(unit0, 0, domain)
				state.copy(varMap = env + (x -> info))
			})
		for {
			v <- nextVar
			_ <- isOneOf(v, domain)
		} yield v
	}
	
	/** 領域が domain である新規変数を n 個作り返す。 */
	def newVars(n: Int, domain: Domain): FD[Stream[Var]] = replicateM(n)(newVar(domain))
	
	/** 変数 x の領域を返す。 */
	def lookup(x: Var): FD[Domain] = { for { state <- get } yield state.varMap(x).values }
	
	/** 変数 x の領域を domain に変更する。 */
	def update(x: Var, domain: Domain): Constraint = {
		for {
			state <- get
			val env = state.varMap
			val info = env(x)
			_ <- put(state.copy(varMap = env + (x -> info.copy(values = domain))))
			_ <- info.delayedConstraints // アーク整合 (AC-2アルゴリズム)
		} yield unit0
	}
	
	/** 変数 x に制約 constraint を追加する。 */
	def addConstraint(x: Var, constraint: Constraint): Constraint = {
		for {
			state <- get
			val env = state.varMap
			val info = env(x)
			val orgConst = info.delayedConstraints
			_ <- put(state.copy(varMap = env + (x -> info.copy(
						delayedConstraints = orgConst flatMap { _ => constraint }, 
						countOfConstraints = info.countOfConstraints + 1
					))))
		} yield unit0
	}
	
//	/* 二項制約が満たされた場合、もう一方の変数に関して同じ制約をチェックする必要はなくなる。 */
//	def decreaseCountIfConstraintIsSatisfied(constraint: Constraint)(x: Var): Constraint = {
//		for {
//			_ <- constraint
//			_ <- modify(state => {
//					val env = state.varMap
//					val info = env(x)
//					state.copy(varMap = env + (x -> info.copy(countOfConstraints = info.countOfConstraints - 1)))
//				})
//		} yield unit0
//	}
	
	/** 二項制約をその対象となる変数に課す。 */
	def createBinaryConstraint(x: Var, y: Var)(constraint: Constraint): Constraint = {
		for {
//			// 制約ネットワークを記録
//			_ <- for {
//				state <- get
//				val network = state.network
//				_ <- put(state.copy(network = ("%d -- %d;". format(x.index, y.index)) :: network))
//			} yield unit0
			_ <- constraint
			_ <- addConstraint(x, constraint)
			_ <- addConstraint(y, constraint)
		} yield unit0
	}
	
	/** 三項制約をその対象となる変数に課す。 */
	def createTrinaryConstraint(x: Var, y: Var, z: Var)(yzConstraint: Constraint, zxConstraint: Constraint, xyConstraint: Constraint): Constraint = {
		for {
//			// 制約ネットワークを記録
//			_ <- for {
//				state <- get
//				val network = state.network
//				_ <- put(state.copy(network = ("%d -- %d;". format(x.index, y.index)) :: ("%d -- %d;". format(y.index, z.index)) :: ("%d -- %d;". format(z.index, x.index)) :: network))
//			} yield unit0
			_ <- yzConstraint
			_ <- zxConstraint
			_ <- xyConstraint
			_ <- addConstraint(x, zxConstraint)
			_ <- addConstraint(x, xyConstraint)
			_ <- addConstraint(y, xyConstraint)
			_ <- addConstraint(y, yzConstraint)
			_ <- addConstraint(z, yzConstraint)
			_ <- addConstraint(z, zxConstraint)
		} yield unit0
	}
	
	/** 変数 x が値 value に等しいという制約を返す。 */
	def hasValue(x: Var, value: Int): Constraint = {
		for {
			vals <- lookup(x)
			_ <- guard(vals.contains(value))
			_ <- when (vals.size != 1) { update(x, Domain(value)) }
		} yield unit0
	}
	
	/** 変数 x が値 value に等しくないという制約を返す。 */
	def hasNotValue(x: Var, value: Int): Constraint = {
		for {
			vals <- lookup(x)
			_ <- guard(vals.size != 1 || ! vals.contains(value))
			_ <- when (vals.contains(value)) { update(x, vals - value) }
		} yield unit0
	}
	
	/** 二つの変数の値が同じであるという制約を返す。 */
	def same(x: Var, y: Var): Constraint = createBinaryConstraint(x, y) {
		for {
			xv <- lookup(x)
			yv <- lookup(y)
			val i = xv & yv
			_ <- guard(! i.isEmpty)
			_ <- when (i != xv) { update(x, i) }
			_ <- when (i != yv) { update(y, i) }
		} yield unit0
	}
	
	/** 二つの変数の値が異なるという制約を返す。 */
	def different(x: Var, y: Var): Constraint = createBinaryConstraint(x, y) {
		for {
			xv <- lookup(x)
			yv <- lookup(y)
			_ <- guard(xv.size != 1 || yv.size != 1 || xv != yv)
			_ <- when (xv.size == 1 && xv.subsetOf(yv)) { update(y, yv -- xv) }
			_ <- when (yv.size == 1 && yv.subsetOf(xv)) { update(x, xv -- yv) }
		} yield unit0
	}
	
	/** 変数 xs の値がすべて異なるという制約を返す。 */
	def allDifferent(xs: Stream[Var]): Constraint = xs match {
		case x #:: xs => for {
				_ <- mapM(xs) { y => different(x, y) }
				_ <- allDifferent(xs)
			} yield unit0
		case Stream.Empty => unit0
	}
	
	/** 変数 x の値 < 変数 y の値という制約を返す。 */
	def lessThan(x: Var, y: Var): Constraint = createBinaryConstraint(x, y) {
		for {
			xv1 <- lookup(x)
			yv1 <- lookup(y)
			val xv2 = xv1.filter(_ < yv1.max)
			val yv2 = yv1.filter(_ > xv1.min)
			_ <- guard(! xv2.isEmpty)
			_ <- guard(! yv2.isEmpty)
			_ <- when (xv1 != xv2) { update(x, xv2) }
			_ <- when (yv1 != yv2) { update(y, yv2) }
		} yield unit0
	}
	
	/** 算術演算後の領域を求める関数 */
	type DomainOperator = ((Domain, Domain) => Domain)
	
	/**
	 * 変数 lhs と変数 rhs 対する算術結果が変数 ans に一致するという制約を返す。
	 * @param ans 算術結果
	 * @param lhs 算術演算の左辺
	 * @param rhs 算術演算の右辺
	 * @param ansDomain lhs と rhs の領域から ans の領域を求める関数
	 * @param lhsDomain ans と rhs の領域から lhs の領域を求める関数
	 * @param rhsDomain ans と lhs の領域から rhs の領域を求める関数
	 * @return 変数 lhs と変数 rhs 対する算術結果が変数 ans に一致するという制約
	 */
	def createArithmeticConstraint(ans: Var)(lhs: Var, rhs: Var)(ansDomain: DomainOperator, lhsDomain: DomainOperator, rhsDomain: DomainOperator): Constraint = {
		def constraint(ans: Var)(lhs: Var, rhs: Var)(domain: DomainOperator): Constraint = {
			for {
				av <- lookup(ans)
				lv <- lookup(lhs)
				rv <- lookup(rhs)
				val newAv = av & domain(lv, rv)
				_ <- guard(! newAv.isEmpty)
				_ <- when (newAv != av) { update(ans, newAv) }
			} yield unit0
		}
		
		createTrinaryConstraint(ans, lhs, rhs)(
			constraint(ans)(lhs, rhs)(ansDomain), 
			constraint(lhs)(ans, rhs)(lhsDomain), 
			constraint(rhs)(ans, lhs)(rhsDomain)
		)
	}
	
	/** lhs + rhs の計算結果の領域を返す。 */
	def addDomain(lhs: Domain, rhs: Domain): Domain = {
		Domain(lhs.min + rhs.min, lhs.max + rhs.max)
	}
	
	/** lhs - rhs の計算結果の領域を返す。 */
	def subDomain(lhs: Domain, rhs: Domain): Domain = {
		Domain(lhs.min - rhs.max, lhs.max - rhs.min)
	}
	
	/** lhs * rhs の計算結果の領域を返す。 */
	def mulDomain(lhs: Domain, rhs: Domain): Domain = {
		var min = maxDomainValue
		var max = minDomainValue
		for (l <- lhs) {
			for (r <- rhs) {
				val mul = l * r
				if (mul < min) min = mul
				if (mul > max) max = mul
			}
		}
		Domain(min, max)
	}
	
	/** lhs / rhs の計算結果の領域を返す。 */
	def divDomain(lhs: Domain, rhs: Domain): Domain = {
		var min = maxDomainValue
		var max = minDomainValue
		try {
			for (r <- rhs) {
				for (l <- lhs) {
					val mul = l / r
					if (mul < min) min = mul
					if (mul > max) max = mul
				}
			}
		} catch {
		  case _: ArithmeticException =>
			  min = minDomainValue
			  max = maxDomainValue
		}
		Domain(min, max)
	}
	
	/** ans が lhs + rhs に等しいという制約を返す。 */
	def equalToAddOf(ans: Var)(lhs: Var, rhs: Var): Constraint = createArithmeticConstraint(ans)(lhs, rhs)(addDomain, subDomain, subDomain)
	
	/** ans が lhs - rhs に等しいという制約を返す。 */
	def equalToSubOf(ans: Var)(lhs: Var, rhs: Var): Constraint = createArithmeticConstraint(ans)(lhs, rhs)(subDomain, addDomain, (l, r) => subDomain(r, l))
	
	/** ans が lhs * rhs に等しいという制約を返す。 */
	def equalToMulOf(ans: Var)(lhs: Var, rhs: Var): Constraint = createArithmeticConstraint(ans)(lhs, rhs)(mulDomain, divDomain, divDomain)
	
	/** ans が lhs / rhs に等しいという制約を返す。 */
	def equalToDivOf(ans: Var)(lhs: Var, rhs: Var): Constraint = createArithmeticConstraint(ans)(lhs, rhs)(divDomain, mulDomain, divDomain)
	
	/** sum が xs の合計に等しいという制約を返す。 */
	def equalToSumOf(sum: Var)(xs: Stream[Var]): Constraint = xs match {
		case Stream.Empty => unit0
		case x #:: Stream.Empty => for {
			_ <- same(x, sum)
		} yield unit0
		case x #:: xs2 => for {
			xv <- lookup(x)
			sv <- lookup(sum)
			newSum <- newVar(subDomain(sv, xv))
			_ <- equalToAddOf(sum)(x, newSum)
			_ <- equalToSumOf(newSum)(xs2)
		} yield unit0
	}
	
	def createAnswerVarOfArithmeticOperation(lhs: Var, rhs: Var)(ansDomain: DomainOperator)(constraintToAnswer: Var => Constraint): FD[Var] = {
		for {
			lv <- lookup(lhs)
			rv <- lookup(rhs)
			ans <- newVar(ansDomain(lv, rv))
			_ <- constraintToAnswer(ans)
		} yield ans
	}
	
	/** lhs + rhs の計算結果に等しい変数を返す。 */
	def add(lhs: Var, rhs: Var): FD[Var] = createAnswerVarOfArithmeticOperation(lhs, rhs)(addDomain)(equalToAddOf(_)(lhs, rhs))
	
	/** lhs - rhs の計算結果に等しい変数を返す。 */
	def sub(lhs: Var, rhs: Var): FD[Var] = createAnswerVarOfArithmeticOperation(lhs, rhs)(subDomain)(equalToSubOf(_)(lhs, rhs))
	
	/** lhs * rhs の計算結果に等しい変数を返す。 */
	def mul(lhs: Var, rhs: Var): FD[Var] = createAnswerVarOfArithmeticOperation(lhs, rhs)(mulDomain)(equalToMulOf(_)(lhs, rhs))
	
	/** lhs / rhs の計算結果に等しい変数を返す。 */
	def div(lhs: Var, rhs: Var): FD[Var] = createAnswerVarOfArithmeticOperation(lhs, rhs)(divDomain)(equalToDivOf(_)(lhs, rhs))
	
	/** lhs + rhs の計算結果に等しい変数を返す。 */
	def add(lhs: Int, rhs: Var): FD[Var] = {
		def constraint(ans: Var)(rhs: Var)(domain: Domain => Domain): Constraint = {
			for {
				av <- lookup(ans)
				rv <- lookup(rhs)
				val newAv = av & domain(rv)
				_ <- guard(! newAv.isEmpty)
				_ <- when (newAv != av) { update(ans, newAv) }
			} yield unit0
		}
		
		for {
			rv <- lookup(rhs)
			ans <- newVar(rv map { _ + lhs })
			val ac = constraint(ans)(rhs)(vals => vals map { _ + lhs }) 
			val rc = constraint(rhs)(ans)(vals => vals map { _ - lhs })
			_ <- ac
			_ <- rc
			_ <- addConstraint(ans, rc)
			_ <- addConstraint(rhs, ac)
		} yield ans
	}
	
	/** lhs * rhs の計算結果に等しい変数を返す。 */
	def mul(lhs: Int, rhs: Var): FD[Var] = {
		def constraint(ans: Var)(rhs: Var)(domain: Domain => Domain): Constraint = {
			for {
				av <- lookup(ans)
				rv <- lookup(rhs)
				val newAv = av & domain(rv)
				_ <- guard(! newAv.isEmpty)
				_ <- when (newAv != av) { update(ans, newAv) }
			} yield unit0
		}
		
		for {
			rv <- lookup(rhs)
			ans <- newVar(rv map { _ * lhs })
			val ac = constraint(ans)(rhs)(vals => vals map { _ * lhs }) 
			val rc = constraint(rhs)(ans)(vals => if (lhs != 0) { vals map { _ / lhs } } else { allDomainValue })
			_ <- ac
			_ <- rc
			_ <- addConstraint(ans, rc)
			_ <- addConstraint(rhs, ac)
		} yield ans
	}
	
	/** 内部 DSL */
	object dsl {
		/** Var にメソッドを追加する暗黙の型変換 */
		implicit def enrichVar(x: Var): RichVar = new RichVar(x)
		
		/** FD[Var] にメソッドを追加する暗黙の型変換 */
		implicit def enrichFDVar(x: FD[Var]): RichFDVar = new RichFDVar(x)
		
		/** Constraint にメソッドを追加する暗黙の型変換 */
		implicit def enrichVarConstraint(constraint: Constraint): RichConstraint = new RichConstraint(constraint)
		
		/** Int にメソッドを追加する暗黙の型変換 */
		implicit def enrichInt(x: Int): RichInt = new RichInt(x)
		
		/** Range から Domain への暗黙の型変換 */
		implicit def rangeToDomain(range: Range): Domain = Domain(range.start, range.end)
		
		/** Int から Domain への暗黙の型変換 */
		implicit def intToDomain(value: Int): Domain = Domain(value)
		
		/** Var にメソッドを追加したクラス */
		class RichVar(x: Var) {
			def <(rhs: Var): Constraint = lessThan(x, rhs)
			def ===(rhs: Var): Constraint = same(x, rhs)
			def !==(rhs: Var): Constraint = different(x, rhs)
			def +(rhs: Var): FD[Var] = add(x, rhs)
			def -(rhs: Var): FD[Var] = sub(x, rhs)
			def *(rhs: Var): FD[Var] = mul(x, rhs)
			def /(rhs: Var): FD[Var] = div(x, rhs)
			
			def <(rhs: FD[Var]): Constraint = for { r <- rhs; _ <- lessThan(x, r) } yield unit0
			def ===(rhs: FD[Var]): Constraint = for { r <- rhs; _ <- same(x, r) } yield unit0
			def !==(rhs: FD[Var]): Constraint = for { r <- rhs; _ <- different(x, r) } yield unit0
			def +(rhs: FD[Var]): FD[Var] = for { r <- rhs; ans <- add(x, r) } yield ans
			def -(rhs: FD[Var]): FD[Var] = for { r <- rhs; ans <- sub(x, r) } yield ans
			def *(rhs: FD[Var]): FD[Var] = for { r <- rhs; ans <- mul(x, r) } yield ans
			def /(rhs: FD[Var]): FD[Var] = for { r <- rhs; ans <- div(x, r) } yield ans
			
			def ===(rhs: Int): Constraint = hasValue(x, rhs)
			def !==(rhs: Int): Constraint = hasNotValue(x, rhs)
		}
		
		/** FD[Var] にメソッドを追加したクラス */
		class RichFDVar(x: FD[Var]) {
			def <(rhs: Var): Constraint = for { l <- x; _ <- lessThan(l, rhs)} yield unit0
			def ===(rhs: Var): Constraint = for { l <- x; _ <- same(l, rhs)} yield unit0
			def !==(rhs: Var): Constraint = for { l <- x; _ <- different(l, rhs)} yield unit0
			def +(rhs: Var): FD[Var] = for { l <- x; ans <- add(l, rhs)} yield ans
			def -(rhs: Var): FD[Var] = for { l <- x; ans <- sub(l, rhs)} yield ans
			def *(rhs: Var): FD[Var] = for { l <- x; ans <- mul(l, rhs)} yield ans
			def /(rhs: Var): FD[Var] = for { l <- x; ans <- div(l, rhs)} yield ans
			
			def <(rhs: FD[Var]): Constraint = for { l <- x; r <- rhs; _ <- lessThan(l, r) } yield unit0
			def ===(rhs: FD[Var]): Constraint = for { l <- x; r <- rhs; _ <- same(l, r) } yield unit0
			def !==(rhs: FD[Var]): Constraint = for { l <- x; r <- rhs; _ <- different(l, r) } yield unit0
			def +(rhs: FD[Var]): FD[Var] = for { l <- x; r <- rhs; ans <- add(l, r) } yield ans
			def -(rhs: FD[Var]): FD[Var] = for { l <- x; r <- rhs; ans <- sub(l, r) } yield ans
			def *(rhs: FD[Var]): FD[Var] = for { l <- x; r <- rhs; ans <- mul(l, r) } yield ans
			def /(rhs: FD[Var]): FD[Var] = for { l <- x; r <- rhs; ans <- div(l, r) } yield ans
			
			def ===(rhs: Int): Constraint = for { l <- x; _ <- hasValue(l, rhs) } yield unit0
			def !==(rhs: Int): Constraint = for { l <- x; _ <- hasNotValue(l, rhs) } yield unit0
		}
		
		/** Constraint にメソッドを追加したクラス */
		class RichConstraint(constraint: Constraint) {
			def ||(rhs: Constraint): Constraint = mplus(constraint, rhs)
		}
		
		/** Int にメソッドを追加したクラス */
		class RichInt(x: Int) {
			def *(rhs: Var): FD[Var] = mul(x, rhs)
			def +(rhs: Var): FD[Var] = add(x, rhs)
			def *(rhs: FD[Var]): FD[Var] = for { r <- rhs; ans <- mul(x, r) } yield ans
		}
	}
	
	/** 変数リスト xs の値リストを返す。 */
	def labeling(xs: Stream[Var]): FD[Stream[Int]] = {
		val indefiniteVars = xs.toSet
		
		// 動的な変数順序のヒューリスティクス
		def label: FD[(Var, Int)] = {
			for {
				state <- get
				x <- {
					var smallestDomainSize = Integer.MAX_VALUE
					var smallestDomainConstraintSize = -1
					var smallestDomainVar: Var = null
					val indefiniteVars = state.indefiniteVars
					for (x <- indefiniteVars) {
						val info = state.varMap(x)
						val size = info.values.size
//						if (info.countOfConstraints > smallestDomainConstraintSize || (info.countOfConstraints == smallestDomainConstraintSize && size < smallestDomainSize)) {
						if (size < smallestDomainSize || (size == smallestDomainSize && info.countOfConstraints > smallestDomainConstraintSize)) {
							smallestDomainSize = size
							smallestDomainConstraintSize = info.countOfConstraints
							smallestDomainVar = x
						}
					}
					//println("smallestDomainVar: " + smallestDomainVar + ", size: " + smallestDomainSize)
					unit(smallestDomainVar)
				}
				_ <- put(state.copy(indefiniteVars = state.indefiniteVars - x))
				vals <- lookup(x)
				v <- lift(vals.toStream)
				_ <- hasValue(x, v)
			} yield (x, v)
		}
		for {
			_ <- modify(state => state.copy(indefiniteVars = indefiniteVars))
			varVals <- replicateM(indefiniteVars.size) { label }
			val valForVar = varVals.toMap
		} yield (xs map { x => valForVar(x) })
		
//		def label(x: Var): FD[Int] = {
//			for {
//				vals <- lookup(x)
//				v <- lift(vals.toStream)
//				_ <- hasValue(x, v)
//			} yield v
//		}
//		mapM(xs) { label }
	}
}
