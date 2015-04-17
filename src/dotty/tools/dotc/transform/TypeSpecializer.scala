package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.TreeTypeMap
import dotty.tools.dotc.ast.Trees.SeqLiteral
import dotty.tools.dotc.ast.tpd._
import dotty.tools.dotc.core.Annotations.Annotation
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.DenotTransformers.InfoTransformer
import dotty.tools.dotc.core.Names.TermName
import dotty.tools.dotc.core.Symbols.{TermSymbol, Symbol}
import dotty.tools.dotc.core.{Symbols, Flags}
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, MiniPhaseTransform}
import dotty.tools.dotc.core.Decorators._
import scala.collection.mutable

class TypeSpecializer extends MiniPhaseTransform  with InfoTransformer {
  
  override def phaseName = "specialize"

  final val maxTparamsToSpecialize = 2

  private val specializationRequests: mutable.HashMap[Symbols.Symbol, List[List[Type]]] = mutable.HashMap.empty

  private var newSymbolMap : mutable.HashMap[TermName, TermSymbol] = mutable.HashMap.empty

  override def transformInfo(tp: Type, sym: Symbol)(implicit ctx: Context): Type = {
    tp match {
      case poly: PolyType  if !(sym.isPrimaryConstructor
                              || (sym is Flags.Label)) =>
        /*val st = shouldSpecializeFor(sym)
          val stt = st.flatten
          val specTypes = stt.filter(stpe => poly.paramBounds.contains(stpe))
        if (!specTypes.isEmpty) {
          println("yay")
        }*/
        println(poly.hasAnnotation(ctx.definitions.specializedAnnot))
        val specTypes = specialisedTypeToSuffix.keys.toList
        val names =  specTypes.map(stpe => specialisedTypeToSuffix(ctx)(stpe))
        val newSym = ctx.newSymbol(sym.owner, (sym.name + names.mkString).toTermName, sym.flags | Flags.Synthetic, poly.instantiate(specTypes))
        //if (!newSym.is(Flags.Frozen)) ctx.enter(newSym)
        ctx.enter(newSym)
        //newSymbolMap++=(mutable.Map(sym, newSym))
        newSym.info
      case _ =>
        tp
    }
    //ctx.newSymbol(tree.symbol.owner, (tree.name + names.mkString).toTermName, tree.symbol.flags | Flags.Synthetic, poly.instantiate(instatiations.toList))
  }

  def registerSpecializationRequest(method: Symbols.Symbol)(arguments: List[Type])(implicit ctx: Context) = {
    if(ctx.phaseId > this.treeTransformPhase.id)
      assert(ctx.phaseId <= this.treeTransformPhase.id)
    val prev = specializationRequests.getOrElse(method, List.empty)
    specializationRequests.put(method, arguments :: prev)
  }

  private final def nameToSpecialisedType(implicit ctx: Context) =
    Map("Byte" -> ctx.definitions.ByteType,
      "Boolean" -> ctx.definitions.BooleanType,
      "Short" -> ctx.definitions.ShortType,
      "Int" -> ctx.definitions.IntType,
      "Long" -> ctx.definitions.LongType,
      "Float" -> ctx.definitions.FloatType,
      "Double" -> ctx.definitions.DoubleType,
      "Char" -> ctx.definitions.CharType,
      "Unit" -> ctx.definitions.UnitType)

  private final def specialisedTypeToSuffix(implicit ctx: Context) =
    Map(ctx.definitions.ByteType -> "$mcB$sp",
    ctx.definitions.BooleanType -> "$mcZ$sp",
    ctx.definitions.ShortType -> "$mcS$sp",
    ctx.definitions.IntType -> "$mcI$sp",
    ctx.definitions.LongType -> "$mcJ$sp",
    ctx.definitions.FloatType -> "$mcF$sp",
    ctx.definitions.DoubleType -> "$mcD$sp",
    ctx.definitions.CharType -> "$mcC$sp",
    ctx.definitions.UnitType -> "$mcV$sp")

  def specializeForAll(sym: Symbols.Symbol)(implicit ctx: Context): List[List[Type]] = {
    registerSpecializationRequest(sym)(specialisedTypeToSuffix.keys.toList)
    println("Specializing for all primitive types")
    specializationRequests.getOrElse(sym, Nil)
  }

  def specializeForSome(sym: Symbols.Symbol)(annotationArgs: List[Type])(implicit ctx: Context): List[List[Type]] = {
    registerSpecializationRequest(sym)(annotationArgs)
    println(s"specializationRequests : $specializationRequests")
    specializationRequests.getOrElse(sym, Nil)
  }

  def shouldSpecializeFor(sym: Symbols.Symbol)(implicit ctx: Context): List[List[Type]] = {
      sym.denot.getAnnotation(ctx.definitions.specializedAnnot).getOrElse(Nil) match {
        case annot: Annotation =>
          annot.arguments match {
            case List(SeqLiteral(types)) =>
              specializeForSome(sym)(types.map(tpeTree =>
                nameToSpecialisedType(ctx)(tpeTree.tpe.asInstanceOf[TermRef].name.toString())))
            case List() => specializeForAll(sym)
          }
        case nil =>
          if(ctx.settings.Yspecialize.value == "all") specializeForAll(sym)
          else Nil
      }
  }

  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    tree.tpe.widen match {

      case poly: PolyType if !(tree.symbol.isPrimaryConstructor
                               || (tree.symbol is Flags.Label)) => {
        val origTParams = tree.tparams.map(_.symbol)
        val origVParams = tree.vparamss.flatten.map(_.symbol)
        println(s"specializing ${tree.symbol} for Tparams: $origTParams")

        def specialize(instantiations: List[Type], name: TermName): Tree = {
          newSymbolMap(name) match {
            case newSym =>
              polyDefDef(newSym, { tparams => vparams => {
                assert(tparams.isEmpty)
                new TreeTypeMap(
                  typeMap = _
                    .substDealias(origTParams, instantiations.toList)
                    .subst(origVParams, vparams.flatten.map(_.tpe)),
                  oldOwners = tree.symbol :: Nil,
                  newOwners = newSym :: Nil
                ).transform(tree.rhs)
              }
              })
            case nil =>
              ctx.error(s"New Symbol for method $name during $phaseName not initialized correctly.")
              EmptyTree // TODO change default behaviour
          }
          //ctx.newSymbol(tree.symbol.owner, (tree.name + names.mkString).toTermName, tree.symbol.flags | Flags.Synthetic, poly.instantiate(instantiations.toList))
        }

        def generateSpecializations(remainingTParams: List[TypeDef], remainingBounds: List[TypeBounds])
                                  (instantiations: List[Type], name: TermName): Iterable[Tree] = {
          if (remainingTParams.nonEmpty) {
            val typeToSpecialize = remainingTParams.head
            val bounds = remainingBounds.head
            shouldSpecializeFor(typeToSpecialize.symbol)
              .flatten
              .filter{ tpe =>
              bounds.contains(tpe)
            }.flatMap { tpe =>
              generateSpecializations(remainingTParams.tail, remainingBounds.tail)(tpe :: instantiations, name)
            }
          }
          else {
            List(specialize(instantiations.reverse, name))
          }
        }
        Thicket(tree :: generateSpecializations(tree.tparams, poly.paramBounds)(List.empty, tree.name).toList)
      }
      case _ => tree
    }
  }

  def transformTypeOfTree(tree: Tree): Tree = {
    tree
  }

  override def transformIdent(tree: Ident)(implicit ctx: Context, info: TransformerInfo): Tree = transformTypeOfTree(tree)
  override def transformSelect(tree: Select)(implicit ctx: Context, info: TransformerInfo): Tree = transformTypeOfTree(tree)

}