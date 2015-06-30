package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.{tpd, TreeTypeMap}
import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.DenotTransformers.InfoTransformer
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.{NameOps, Symbols, Flags}
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, MiniPhaseTransform}
import scala.collection.mutable
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools._

import scala.collection.mutable.ListBuffer

class TypeSpecializer extends MiniPhaseTransform  with InfoTransformer {

  import tpd._
  override def phaseName = "specialize"

  final var maxTparamsToSpecialize = 0

  private def primitiveTypes(implicit ctx: Context) =
    List(defn.ByteType,
      defn.BooleanType,
      defn.ShortType,
      defn.IntType,
      defn.LongType,
      defn.FloatType,
      defn.DoubleType,
      defn.CharType,
      defn.UnitType)

  private def defn(implicit ctx:Context) = ctx.definitions

  private val specializationRequests: mutable.HashMap[Symbols.Symbol, List[(Int, List[Type])]] = mutable.HashMap.empty
  private val genericToInstantiation: mutable.HashMap[Symbols.Symbol, Type] = mutable.HashMap.empty
  /**
   *  A map that links symbols to their specialized variants.
   *  Each symbol maps to another map, from the list of specialization types to the specialized symbol.
   */
  private val newSymbolMap: mutable.HashMap[Symbol, mutable.HashMap[List[(Int, Type)], Symbols.Symbol]] = mutable.HashMap.empty
  private val symToInstTypes: mutable.HashMap[Symbol, List[Type]] = mutable.HashMap.empty

  def allowedToSpecialize(sym: Symbol, numOfTypes: Int)(implicit ctx: Context): Boolean = {
    (maxTparamsToSpecialize == 0 || numOfTypes <= maxTparamsToSpecialize) &&
      numOfTypes > 0 &&
      sym.name != nme.asInstanceOf_ &&
      sym.name != nme.isInstanceOf_ &&
      !(sym is Flags.JavaDefined) &&
      !sym.isConstructor
  }

  def getSpecTypes(method: Symbol, poly: PolyType)(implicit ctx: Context): List[(Int, List[Type])] = {

    val requested = specializationRequests.getOrElse(method, List.empty).toMap
    if (requested.nonEmpty) {
      poly.paramNames.zipWithIndex.map{
        case(name, i) if requested.contains(i) => (i, requested(i))
        case(name, i) => (i, Nil)
      }
    }
    else {
      if (ctx.settings.Yspecialize.value == "all") {
        val filteredPrims = primitiveTypes.filter(tpe => poly.paramBounds.forall(_.contains(tpe)))
        List.range(0, poly.paramNames.length - 1).map(i => (i, filteredPrims))
      }
      else Nil
    }
  }

  def requestedSpecialization(decl: Symbol)(implicit ctx: Context): Boolean =
    specializationRequests.contains(decl) ||
      (ctx.settings.Yspecialize.value != "" && decl.name.contains(ctx.settings.Yspecialize.value)) ||
      ctx.settings.Yspecialize.value == "all"

  def registerSpecializationRequest(method: Symbols.Symbol)(index: Int, arguments: List[Type])(implicit ctx: Context) = {
    if (ctx.phaseId > this.treeTransformPhase.id)
      assert(ctx.phaseId <= this.treeTransformPhase.id)
    val prev = specializationRequests.getOrElse(method, List.empty)
    specializationRequests.put(method, (index, arguments) :: prev)
  }

  override def transformInfo(tp: Type, sym: Symbol)(implicit ctx: Context): Type = {
    def generateSpecializations(specTypes: List[(Int, List[Type])])
                               (instantiations: List[(Int, Type)], poly: PolyType, decl: Symbol)
                               (implicit ctx: Context): List[Symbol] = {
      if (specTypes.nonEmpty) {
        specTypes.head match{
          case (i, tpes) if tpes.nonEmpty =>
            tpes.flatMap(tpe =>
              generateSpecializations(specTypes.tail)((i, tpe) :: instantiations, poly, decl)
            )
          case (i, nil) =>
            generateSpecializations(specTypes.tail)(instantiations, poly, decl)
        }
      }
      else {
        if (instantiations.isEmpty) Nil
        else generateSpecializedSymbol(instantiations.reverse, poly, decl) :: Nil
      }
    }
    def generateSpecializedSymbol(instantiations: List[(Int, Type)], poly: PolyType, decl: Symbol)
                                  (implicit ctx: Context): Symbol = {
      val indices = instantiations.map(_._1)
      val instanceTypes = instantiations.map(_._2)
      val newSym = ctx.newSymbol(decl.owner, NameOps.NameDecorator(decl.name).specializedFor(null, Nil, instanceTypes),
                   decl.flags | Flags.Synthetic, {
        if (indices.length != poly.paramNames.length) // Partial Specialisation case
          poly.instantiate(indices, instanceTypes) // Returns a PolyType with uninstantiated types kept generic
        else
          poly.instantiate(instanceTypes) // Returns a MethodType, as no polymorphic types remain
      })

      /* The following generated symbols which kept type bounds. It served as a way of keeping type bounds in cases such
       * as those discussed in issue #592. However, because type bounds are not transitive, this did not work out and we
       * introduced casts instead.
       *
       * ctx.newSymbol(decl.owner, (decl.name + names.mkString).toTermName,
       *               decl.flags | Flags.Synthetic,
       *               poly.derivedPolyType(poly.paramNames,
       *                                    (poly.paramBounds zip instanceTypes.map(_.widen)).map
       *                                             {case (bounds, it) =>
       *                                               TypeBounds(bounds.lo, AndType(bounds.hi, it))},
       *                                    poly.instantiate(indices, instanceTypes.map(_.widen))
       *                                    )
       *               )
       */

      val map = newSymbolMap.getOrElse(decl, mutable.HashMap.empty)
      map.put(instantiations, newSym)
      newSymbolMap.put(decl, map)
      newSym
    }

    if ((sym ne defn.ScalaPredefModule.moduleClass) &&
      !(sym is Flags.JavaDefined) &&
      !(sym is Flags.Scala2x) &&
      !(sym is Flags.Package) &&
      !sym.isAnonymousClass) {
      sym.info match {
        case classInfo: ClassInfo =>
          val newDecls = classInfo.decls
            .filter(_.symbol.isCompleted) // we do not want to force symbols here.
                                          // if there's unforced symbol it means its not used in the source
            .filterNot(_.isConstructor)
            .filter(requestedSpecialization)
            .flatMap(decl => {
            decl.info.widen match {
              case poly: PolyType if allowedToSpecialize(decl.symbol, poly.paramNames.length) =>
                generateSpecializations(getSpecTypes(decl, poly))(List.empty, poly, decl)
              case _ => Nil
            }
          })

          if (newDecls.nonEmpty) {
            val decls = classInfo.decls.cloneScope
            newDecls.foreach(decls.enter)
            classInfo.derivedClassInfo(decls = decls)
          }
          else tp
        case poly: PolyType if !newSymbolMap.contains(sym)&&
          requestedSpecialization(sym) &&
          allowedToSpecialize(sym, poly.paramNames.length) =>
            generateSpecializations(getSpecTypes(sym, poly))(List.empty, poly, sym)
            tp
        case _ => tp
      }
    } else tp
  }

  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    tree.tpe.widen match {

      case poly: PolyType if !(tree.symbol.isConstructor
        || (tree.symbol is Flags.Label))
        || (tree.symbol.name == nme.asInstanceOf_) =>
        val origTParams = tree.tparams.map(_.symbol)
        val origVParams = tree.vparamss.flatten.map(_.symbol)

        def specialize(decl : Symbol): List[Tree] = {

          def fullTypesList(origTSyms: List[Symbol], instantiation: Map[Int, Type], pt: PolyType): List[Type] = {
            var holePos = -1
            origTSyms.zipWithIndex.map {
              case (_, i) => instantiation.getOrElse(i, {
                holePos += 1
                PolyParam(pt, holePos)
              }
              ).widen
            }
          }

          if (newSymbolMap.contains(decl)) {
            val declSpecs = newSymbolMap(decl)
            val newSyms = declSpecs.values.toList
            val instantiations = declSpecs.keys.toArray
            var index = -1
            ctx.debuglog(s"specializing ${tree.symbol} for $origTParams")
            newSyms.map { newSym =>
              index += 1
              val newSymType = newSym.info.widenDealias
              polyDefDef(newSym.asTerm, { tparams => vparams => {
                val instTypes = newSym.info.widen match {
                  case pt: PolyType => fullTypesList(origTParams, instantiations(index).toMap, pt)
                  case _ => instantiations(index).map(_._2)
                }
                symToInstTypes.put(newSym, instTypes)

                val treemap: (Tree => Tree) = _ match {
                  case Return(t, from) if from.symbol == tree.symbol => Return(t, ref(newSym))
                  case t: TypeApply =>
                    (origTParams zip instTypes).foreach(x => genericToInstantiation.put(x._1, x._2))
                    transformTypeApply(t)
                  case t: Apply =>
                    (origTParams zip instTypes).foreach(x => genericToInstantiation.put(x._1, x._2))
                    transformApply(t)
                  case t => t
                }

                val abstractPolyType = tree.symbol.info.widenDealias.asInstanceOf[PolyType]
                val typemap = new TypeMap {
                  override def apply(tp: Type): Type = {
                    val t = mapOver(tp)
                      .substDealias(origTParams, instTypes)
                      .substParams(abstractPolyType, instTypes)
                      .subst(origVParams, vparams.flatten.map(_.tpe))
                    if (tparams.isEmpty) t else t.substParams(newSymType.asInstanceOf[PolyType], tparams)
                  }
                }

                val typesReplaced = new TreeTypeMap(
                  treeMap = treemap,
                  typeMap = typemap,
                  oldOwners = tree.symbol :: Nil,
                  newOwners = newSym :: Nil
                ).transform(tree.rhs)

                val tp = new TreeMap() {
                  // needed to workaround https://github.com/lampepfl/dotty/issues/592
                  override def transform(tree1: Tree)(implicit ctx: Context) = super.transform(tree1) match {
                    case t @ Apply(fun, args) =>
                      assert(sameLength(args, fun.tpe.widen.firstParamTypes))
                      val newArgs = (args zip fun.tpe.widen.firstParamTypes).map{
                       case(tr, tpe) if !tpe.isInstanceOf[PolyParam] =>
                          tr.ensureConforms(tpe)
                        case (tr, tpe) => tr
                         }
                      if (sameTypes(args, newArgs)) {
                        t
                      } else tpd.Apply(fun, newArgs)
                    case t: ValDef =>
                      cpy.ValDef(t)(rhs = if (t.rhs.isEmpty) EmptyTree else
                        t.rhs.ensureConforms(t.tpt.tpe))
                    case t: DefDef =>
                      cpy.DefDef(t)(rhs = if (t.rhs.isEmpty) EmptyTree else
                        t.rhs.ensureConforms(t.tpt.tpe))
                    case t: TypeTree =>
                      t.tpe match {
                        case pp: PolyParam =>
                          TypeTree(tparams(pp.paramNum))
                        case _ => t
                      }
                    case t => t
                  }}
                val expectedTypeFixed = tp.transform(typesReplaced)
                expectedTypeFixed.ensureConforms(typemap(newSym.info.widen.finalResultType))
              }})
            }
          } else Nil
        }
        val specializedTrees = specialize(tree.symbol)
        Thicket(tree :: specializedTrees)
      case _ => tree
    }
  }

  def rewireTree(tree: Tree)(implicit ctx: Context): Tree = {
    assert(tree.isInstanceOf[TypeApply])
    val TypeApply(fun,args) = tree
    if (newSymbolMap.contains(fun.symbol)){
      val newSymInfos = newSymbolMap(fun.symbol)
      val genericInstantiations: ListBuffer[Type] = ListBuffer.empty
      val betterDefs = newSymInfos.filter(
        x =>
          (x._2.info.widen.paramTypess.flatten zip args)
            .forall{a =>
        val specializedType = a._1
        val argType = genericToInstantiation.getOrElse(a._2.tpe.typeSymbol, a._2.tpe)
        if (specializedType.isInstanceOf[PolyParam]) {
          genericInstantiations += argType
        }
        argType <:< specializedType || specializedType.isInstanceOf[PolyParam]
      }).toList

      if (betterDefs.length > 1) {
        ctx.debuglog(s"Several specialized variants fit for method ${fun.symbol.name} of ${fun.symbol.owner}. Defaulting to no specialization.")
        tree
      }

      else if (betterDefs.nonEmpty) {
        val bestDef = betterDefs.head
        ctx.debuglog(s"method ${fun.symbol.name} of ${fun.symbol.owner} rewired to specialized variant with type(s): " ++
            s"${symToInstTypes(bestDef._2).map{case TypeRef(_, name) => name; case generic => generic}.mkString(", ")}")
        val prefix = fun match {
          case Select(pre, name) =>
            pre
          case t @ Ident(_) if t.tpe.isInstanceOf[TermRef] =>
            val tp = t.tpe.asInstanceOf[TermRef]
            if (tp.prefix ne NoPrefix)
              ref(tp.prefix.termSymbol)
            else EmptyTree
        }
        if (prefix ne EmptyTree) {
          val tree1 = prefix.select(bestDef._2)
          bestDef._2.info match {
            case poly: PolyType =>
              tree1
            case _ => tree1
          }
        }
        else {
          val ret = ref(bestDef._2)
          ret
        }
      } else tree
    } else tree
  }

  override def transformTypeApply(tree: tpd.TypeApply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    val TypeApply(fun, _) = tree
    if (fun.tpe.widen.isParameterless) {
      rewireTree(tree)
    }
    else tree
  }

  override def transformApply(tree: Apply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    val Apply(fun, args) = tree
    fun match {
      case fun: TypeApply =>
        val TypeApply(_, args2) = fun
        val newFun = rewireTree(fun)
        if (fun ne newFun) {
          val partiallySpecialized: Boolean = newFun.tpe.widen.paramTypess.flatten.exists(_.isInstanceOf[PolyParam])
          val pairs = args zip {if (partiallySpecialized) args2.map(_.tpe.widen) else newFun.tpe.widen.paramTypess.flatten}
          val as = pairs.map{
            case (arg, tpe) =>
              arg.ensureConforms(tpe match {
                case tv: TypeVar =>
                  tv.instanceOpt
                case _ =>
                  tpe
              })
          }
          val remainingGenerics: List[(tpd.Tree, Type)] =
            args2.zip(symToInstTypes.getOrElse(newFun.symbol, args.map(_.tpe))).filter(_._2.isInstanceOf[PolyParam])
          if (remainingGenerics.map(_._2).nonEmpty) {
            Apply(TypeApply(newFun, remainingGenerics.map(_._1)), as)
          }
          else Apply(newFun, as)
        } else tree
      case fun : Apply =>
        Apply(transformApply(fun), args)
      case _ => tree
    }
  }
}
