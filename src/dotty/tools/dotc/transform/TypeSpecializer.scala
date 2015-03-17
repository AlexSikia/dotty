package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.TreeTypeMap
import dotty.tools.dotc.ast.tpd._
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Flags
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, MiniPhaseTransform}
import dotty.tools.dotc.core.Decorators._
import scala.collection.mutable.{ListBuffer, ArrayBuffer}

class TypeSpecializer extends MiniPhaseTransform {
  
  override def phaseName = "specialize"

  final val maxTparamsToSpecialize = 2
  
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
  
  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    def rewireType(tpe: Type) = tpe match {
        case tpe: TermRef => tpe.widen
        case _ => tpe
      }
    
    tree.tpe.widen match {
        
      case poly: PolyType if !(tree.symbol.isPrimaryConstructor
                               || (tree.symbol is Flags.Label)
                               || (tree.tparams.length > maxTparamsToSpecialize)) => {
        val origTParams = tree.tparams.map(_.symbol)
        val origVParams = tree.vparamss.flatten.map(_.symbol)
        println(s"specializing ${tree.symbol} for Tparams: ${origTParams.length}")

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
            specialisedTypes.filter{ tpnme =>
              bounds.contains(tpnme._1)
            }.flatMap { tpnme =>
              val tpe = tpnme._1
              val nme = tpnme._2
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