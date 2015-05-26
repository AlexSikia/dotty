package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.{Trees, tpd, TreeTypeMap}
import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Annotations.Annotation
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Decorators.StringDecorator
import dotty.tools.dotc.core.DenotTransformers.InfoTransformer
import dotty.tools.dotc.core.Names.Name
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.{Symbols, Flags}
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, MiniPhaseTransform}
import scala.collection.mutable
import dotty.tools.dotc.core.StdNames.nme

class TypeSpecializer extends MiniPhaseTransform  with InfoTransformer {

  import tpd._
  override def phaseName = "specialize"
  private def defn(implicit ctx:Context) = ctx.definitions
  final val maxTparamsToSpecialize = 2

  private final def specialisedTypeToSuffix(implicit ctx: Context) =
    Map(defn.ByteType -> "$mcB$sp",
      defn.BooleanType -> "$mcZ$sp",
      defn.ShortType -> "$mcS$sp",
      defn.IntType -> "$mcI$sp",
      defn.LongType -> "$mcJ$sp",
      defn.FloatType -> "$mcF$sp",
      defn.DoubleType -> "$mcD$sp",
      defn.CharType -> "$mcC$sp",
      defn.UnitType -> "$mcV$sp")

  private def primitiveTypes(implicit ctx: Context) =
    List(defn.ByteType,
      defn.BooleanType,
      defn.ShortType,
      defn.IntType,
      defn.LongType,
      defn.FloatType,
      defn.DoubleType,
      defn.CharType,
      defn.UnitType
    )

  // Maps generic methods symbols to new symbols of specialized variants
  private val newSymbolMap: mutable.HashMap[Symbol, List[Symbols.Symbol]] = mutable.HashMap.empty
  private val methodsToSpecialize: mutable.Set[Symbol] = mutable.Set.empty
  // Maps generic methods symbols to lists of specialization types and position of generic types to specialize
  // (for partial specialization)
  private val specializationRequests: mutable.HashMap[Symbol, List[(Int, List[Type])]] = mutable.HashMap.empty
  // Maps new symbols of specialized methods to the list of types they are specialized to, and positions of their
  // respective generic types (for partial specialization)
  private val specializationsTParams: mutable.HashMap[Symbol, List[(Int, Type)]] = mutable.HashMap.empty
  // Maps new symbols of specialized methods to the list of types they are specialized to, including generic types
  // in the case of partial specialization
  private val specializationsCompleteTParams: mutable.HashMap[Symbol, List[Type]] = mutable.HashMap.empty

  def allowedToSpecialize(sym: Symbol, numOfTypes: Int)(implicit ctx: Context): Boolean = {
    numOfTypes <= maxTparamsToSpecialize &&
      numOfTypes > 0 &&
      sym.name != nme.asInstanceOf_ &&
      sym.name != nme.isInstanceOf_ &&
      !(sym is Flags.JavaDefined) &&
      !sym.isConstructor &&
      !sym.name.toString.contains("Function2")
  }

  def getSpecTypes(method: Symbol, poly: PolyType, numOfArgs: Int)(implicit ctx: Context): List[(Int, List[Type])] = {
    val requested = specializationRequests(method)
    if (requested.nonEmpty) requested
    else {
      if(ctx.settings.Yspecialize.value == "all") 0.to(numOfArgs).toList.map((_, primitiveTypes.filter(tpe => poly.paramBounds.forall(_.contains(tpe)))))
      else Nil
    }
  }

  def requestedSpecialization(decl: Symbol)(implicit ctx: Context): Boolean =
    methodsToSpecialize.contains(decl) ||
      (ctx.settings.Yspecialize.value != "" && decl.name.contains(ctx.settings.Yspecialize.value)) ||
      ctx.settings.Yspecialize.value == "all"

  def registerSpecializationRequest(method: Symbols.Symbol)(index: Int, arguments: List[Type])(implicit ctx: Context) = {
    assert(arguments.nonEmpty)
    if(ctx.phaseId > this.treeTransformPhase.id)
      assert(ctx.phaseId <= this.treeTransformPhase.id)
    methodsToSpecialize.add(method)
    val prev: List[(Int, List[Type])] = specializationRequests.getOrElse(method, List())
    specializationRequests.put(method, (index, arguments) :: prev)
  }

  override def transformInfo(tp: Type, sym: Symbol)(implicit ctx: Context): Type = {
    def generateSpecializations(remainingTParams: List[Int], specTypesMap: Map[Int, List[Type]])
                               (indices: List[Int], instantiations: List[Type], names: List[String], poly: PolyType, decl: Symbol)
                               (implicit ctx: Context): List[Symbol] = {
      if (remainingTParams.nonEmpty) {
        (for (tpe <- specTypesMap(remainingTParams.head)) yield {
          generateSpecializations(remainingTParams.tail, specTypesMap)(remainingTParams.head :: indices, tpe :: instantiations, specialisedTypeToSuffix(ctx)(tpe) :: names, poly, decl)
        }).flatten
      }
      else {
        generateSpecializedSymbols(indices, instantiations, names, poly, decl)
      }
    }
    def generateSpecializedSymbols(indices: List[Int], instantiations: List[Type], names: List[String], poly: PolyType, decl: Symbol)
                                  (implicit ctx: Context): List[Symbol] = {
      assert(indices.length == instantiations.length)
      val newSymInfo = {
        if (decl.symbol.info.paramTypess.flatten.length == indices.length) poly.instantiate(instantiations)
        else poly.instantiate(indices, instantiations)
      }
      val newSym =
        ctx.newSymbol(decl.owner, (decl.name + names.mkString).toTermName,
                      decl.flags | Flags.Synthetic, newSymInfo)

      /* The following generated symbols which kept type bounds. It served, as illustrated by the `this_specialization`
       * test, as a way of keeping type bounds when instantiating a `this` referring to a generic class. However,
       * because type bounds are not transitive, this did not work out and we introduced casts instead.
       *
       * ctx.newSymbol(decl.owner, (decl.name + names.mkString).toTermName,
       *               decl.flags | Flags.Synthetic,
       *               poly.derivedPolyType(poly.paramNames,
       *                                    (poly.paramBounds zip instantiations).map
       *                                             {case (bounds, instantiation) =>
       *                                               TypeBounds(bounds.lo, AndType(bounds.hi, instantiation))},
       *                                    poly.instantiate(indices, instantiations)
       *                                    )
       *               )
       */

      val prevSyms = newSymbolMap.getOrElse(decl, List())
      newSymbolMap.put(decl, newSym :: prevSyms)
      specializationsTParams.put(newSym, indices zip instantiations)
      newSym :: prevSyms
    }

    if((sym ne defn.ScalaPredefModule.moduleClass) &&
       !(sym is Flags.Package) &&
       !sym.isAnonymousClass) {
      sym.info match {
        case classInfo: ClassInfo =>
          val newDecls = classInfo.decls
            .filterNot(_.isConstructor)
            .filter(requestedSpecialization)
            .flatMap(decl => {
              decl.info.widen match {
                case poly: PolyType if allowedToSpecialize(decl.symbol, specializationRequests(decl).length) =>
                  val requestedSpecs = getSpecTypes(decl, poly, decl.typeParams.length)
                  if (requestedSpecs.nonEmpty)
                    generateSpecializations(requestedSpecs.map(_._1), requestedSpecs.toMap)(List.empty, List.empty, List.empty, poly, decl)
                  else Nil
                case nil => Nil
              }
          })
            val decls = classInfo.decls.cloneScope
            newDecls.foreach(decls.enter)
            classInfo.derivedClassInfo(decls = decls)
        case poly: PolyType if !newSymbolMap.contains(sym) &&
                               requestedSpecialization(sym) &&
                               allowedToSpecialize(sym, specializationRequests(sym).length)=>
          val requestedSpecs = getSpecTypes(sym, poly, sym.typeParams.length)
          if (requestedSpecs.nonEmpty)
            generateSpecializations(requestedSpecs.map(_._1), requestedSpecs.toMap)(List.empty, List.empty, List.empty, poly, sym)
        case nil =>
      }
      tp
    } else tp
  }


  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    tree.tpe.widen match {

      case poly: PolyType if !(tree.symbol.isConstructor ||
        (tree.symbol is Flags.Label)) ||
        (tree.symbol.name == nme.asInstanceOf_) =>

        val origTParams = tree.tparams.map(_.symbol)
        val origVParams = tree.vparamss.flatten.map(_.symbol)

        def specialize(decl : Symbol): List[Tree] = {

          def generateAndStoreTParams(newSym: Symbol, tree: DefDef): List[Type] = {
            val tpars = specializationsTParams(newSym).toMap
            val instantiations  = tree.tparams.zipWithIndex.map { case (origTparam, i) =>
              if (tpars.contains(i)) tpars(i)
              else {
                assert(newSym.info.isInstanceOf[PolyType])
                val newSymPoly = newSym.info.asInstanceOf[PolyType]
                new PolyParam(newSymPoly, i)//findMatching(origTparam, newSym.info.resultType.paramTypess.head))

                /*def findMatching(typeDef: Trees.TypeDef[Type], types: List[Type]): Int = {
                  def findMatchingAcc(typeDef: Trees.TypeDef[Type], types: List[Type], res: Int): Int = {
                    assert(types.nonEmpty)
                    if (types.head eq typeDef.symbol.info) res else findMatchingAcc(typeDef, types.tail, res + 1)
                  }
                  findMatchingAcc(typeDef, types, 0)
                }*/
              }
            }.asInstanceOf[List[Type]]
            if (!specializationsCompleteTParams.contains(newSym)) specializationsCompleteTParams.put(newSym, instantiations)
            instantiations
          }

          if (newSymbolMap.contains(decl)) {
            val newSyms = newSymbolMap(decl)
            println(s"specializing ${tree.symbol} for $origTParams")
            newSyms.map { newSym =>
              polyDefDef(newSym.asTerm, { tparams => vparams => {
                val tmap: (Tree => Tree) = _ match {
                  case Return(t, from) if from.symbol == tree.symbol => Return(t, ref(newSym))
                  case t: TypeApply => transformTypeApply(t)
                  case t: Apply => transformApply(t)
                  case t => t
                }

                val instantiations: List[Type] = generateAndStoreTParams(newSym, tree)

                new TreeTypeMap(
                  treeMap = tmap,
                  typeMap = _
                    .substDealias(origTParams, instantiations)
                    .subst(origVParams, vparams.flatten.map(_.tpe)),
                  oldOwners = tree.symbol :: Nil,
                  newOwners = newSym :: Nil
                ).transform(tree.rhs)
              }})
            }
          } else Nil
        }
        val specialized_trees = specialize(tree.symbol)
        Thicket(tree :: specialized_trees)
      case _ => tree
    }
  }

  override def transformTypeApply(tree: tpd.TypeApply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    //val TypeApply(fun, _) = tree
    /*if (fun.tpe.isParameterless)*/ val x = rewireTree(tree)
    x
    //tree
  }
/*
  override def transformApply(tree: Apply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    val Apply(fun, args) = tree
    fun match {
      case f: TypeApply => {/*
        println(
          s"""
             |args             ->  $args
             |fun.symbol       ->  ${f.args.map(_.symbol)}
             |typeParams       ->  ${f.args.map(_.symbol.info.dealias)}
             |typeParams.info  ->  ${f.args.map(_.symbol.info.bounds)}
           """.stripMargin)*/
        //val a = f.args.map(_.symbol.info.bounds.lo)
        val instantiations = f.args.map(_.tpe)
        val paramTypes = args.tpes.map(_.widen)
        Apply(rewireTree(f),(args ))/*zip (instantiations zip paramTypes)).map{
          case (argType, (specType, castType)) => argType.ensureConforms(TypeApply(castType, specType))})*/
      }
      case _ => tree
    }
  }
*/
  def rewireTree(tree: Tree)(implicit ctx: Context): Tree = {
    assert(tree.isInstanceOf[TypeApply])
    val TypeApply(fun,args) = tree
    if (newSymbolMap.contains(fun.symbol)){
      val newSyms = newSymbolMap(fun.symbol)
      val newSymTypes = newSyms.map(specializationsCompleteTParams)
      val betterDefs = (newSyms zip newSymTypes).filter(x => (x._2 zip args).forall { a =>
        val specializedType = a._1
        val argType = a._2
        argType.tpe <:< specializedType || specializedType.isInstanceOf[PolyParam] // i.e. the specializedType is a subset of the expected type, or it is unspecialized
      })


      if (betterDefs.length > 1) {
        ctx.debuglog("Several specialized variants fit. Defaulting to no specialization.")
        tree
      }
      else if (betterDefs.nonEmpty) {
        val best = betterDefs.head
        println(s"method ${fun.symbol.name} of ${fun.symbol.owner} rewired to specialized variant ${best._1}")
        val prefix = fun match {
          case Select(pre, name) =>
            pre
          case t @ Ident(_) if t.tpe.isInstanceOf[TermRef] =>
            val tp = t.tpe.asInstanceOf[TermRef]
            if (tp.prefix ne NoPrefix)
              ref(tp.prefix.termSymbol)
            else EmptyTree
        }
        if (prefix ne EmptyTree)
          prefix.select(best._1)//.ensureConforms(specType)
        else ref(best._1)//.ensureConforms(specType)
      } else tree
    } else tree
  }
}