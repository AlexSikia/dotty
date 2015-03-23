package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.TreeTypeMap
import dotty.tools.dotc.ast.tpd._
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.{Symbols, Flags}
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, MiniPhaseTransform}
import dotty.tools.dotc.core.Decorators._
import scala.collection.mutable

class TypeSpecializer extends MiniPhaseTransform {
  
  override def phaseName = "specialize"

  final val maxTparamsToSpecialize = 2

  private val specializationRequests: mutable.HashMap[Symbols.Symbol, List[List[Type]]] = mutable.HashMap.empty

  def registerSpecializationRequest(method: Symbols.Symbol)(arguments: List[Type])(implicit ctx: Context) = {
    assert(ctx.phaseId <= this.period.phaseId) // This fails - why ?
    val prev = specializationRequests.getOrElse(method, List.empty)
    specializationRequests.put(method, arguments :: prev)
  }

  private final def specialisedTypes(implicit ctx: Context) =
    Map(ctx.definitions.ByteType -> "$mcB$sp",
    ctx.definitions.BooleanType -> "$mcZ$sp",
    ctx.definitions.ShortType -> "$mcS$sp",
    ctx.definitions.IntType -> "$mcI$sp",
    ctx.definitions.LongType -> "$mcJ$sp",
    ctx.definitions.FloatType -> "$mcF$sp",
    ctx.definitions.DoubleType -> "$mcD$sp",
    ctx.definitions.CharType -> "$mcC$sp",
    ctx.definitions.UnitType -> "$mcV$sp")

  def shouldSpecializeForAll(sym: Symbols.Symbol)(implicit ctx: Context): Boolean = {
    // either -Yspecialize:all is given, or sym has @specialize annotation
    (sym.denot.hasAnnotation(ctx.definitions.specializedAnnot) && true /*check for empty list of types to specialize to*/)|| (ctx.settings.Yspecialize.value == "all")
  }

  def shouldSpecializeForSome(sym: Symbols.Symbol)(implicit ctx: Context): List[List[Type]] = {
    if (sym.denot.hasAnnotation(ctx.definitions.specializedAnnot)) {
      val specAnnotation = sym.denot.getAnnotation(ctx.definitions.specializedAnnot)
      val annotationArgs = List() // How can I get the list of types associated to the @specialized annotation ?
      registerSpecializationRequest(sym)(annotationArgs)
      println(s"specializationRequests : $specializationRequests")
    }
    specializationRequests.getOrElse(sym, Nil)
  }

  def shouldSpecializeFor(sym: Symbols.Symbol)(implicit ctx: Context): List[List[Type]] = {
    if (shouldSpecializeForAll(sym)) {
      registerSpecializationRequest(sym)(specialisedTypes.keys.toList)
      specializationRequests.getOrElse(sym, Nil)
    }
    else shouldSpecializeForSome(sym)
  }

  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    tree.tpe.widen match {
        
      case poly: PolyType if !(tree.symbol.isPrimaryConstructor
                               || (tree.symbol is Flags.Label)) => {
        val origTParams = tree.tparams.map(_.symbol)
        val origVParams = tree.vparamss.flatten.map(_.symbol)
        println(s"specializing ${tree.symbol} for Tparams: ${origTParams}")

        def specialize(instatiations: List[Type], names: List[String]): Tree = {

          val newSym = ctx.newSymbol(tree.symbol.owner, (tree.name + names.mkString).toTermName, tree.symbol.flags | Flags.Synthetic, poly.instantiate(instatiations.toList))
          polyDefDef(newSym, { tparams => vparams => {
            assert(tparams.isEmpty)
            new TreeTypeMap(
              typeMap = _
                .substDealias(origTParams, instatiations.toList)
                .subst(origVParams, vparams.flatten.map(_.tpe)),
              oldOwners = tree.symbol :: Nil,
              newOwners = newSym :: Nil
            ).transform(tree.rhs)
          }
          })
        }

        def generateSpecializations(remainingTParams: List[TypeDef], remainingBounds: List[TypeBounds])
                                  (instatiations: List[Type],
                                    names: List[String]): Iterable[Tree] = {
          if (remainingTParams.nonEmpty) {
            val typeToSpecialize = remainingTParams.head
            val bounds = remainingBounds.head
            val specializeTo = shouldSpecializeFor(typeToSpecialize.symbol).flatten
            println(s"types to specialize for are : $specializeTo")

            specializeTo.filter{ tpe =>
              bounds.contains(tpe)
            }.flatMap { tpe =>
              val nme = specialisedTypes(ctx)(tpe)
              generateSpecializations(remainingTParams.tail, remainingBounds.tail)(tpe :: instatiations, nme :: names)
            }
          } else
            List(specialize(instatiations.reverse, names.reverse))
        }
        Thicket(tree :: generateSpecializations(tree.tparams, poly.paramBounds)(List.empty, List.empty).toList)
      }
      case _ => tree
    }
  }
}