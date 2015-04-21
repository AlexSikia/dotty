package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.{tpd, TreeTypeMap}
import dotty.tools.dotc.ast.Trees.{TypeApply, SeqLiteral}
import dotty.tools.dotc.ast.tpd._
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

class TypeSpecializer extends MiniPhaseTransform  with InfoTransformer {

  override def phaseName = "specialize"

  final val maxTparamsToSpecialize = 2

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

  private def primitiveTypes(implicit ctx: Context) =
    List(ctx.definitions.ByteType,
      ctx.definitions.BooleanType,
      ctx.definitions.ShortType,
      ctx.definitions.IntType,
      ctx.definitions.LongType,
      ctx.definitions.FloatType,
      ctx.definitions.DoubleType,
      ctx.definitions.CharType,
      ctx.definitions.UnitType
    )

  private val specializationRequests: mutable.HashMap[Symbols.Symbol, List[List[Type]]] = mutable.HashMap.empty

  private val newSymbolMap: mutable.HashMap[Symbol, (List[Symbols.Symbol], List[Type])] = mutable.HashMap.empty

  /*private def specializedSymbol(methSym: Symbol): (List[Symbol], List[Type]) = {
    if (newSymbolMap.contains(methSym)) newSymbolMap(methSym)
    else (Nil, Nil)
  }*/

  override def transformInfo(tp: Type, sym: Symbol)(implicit ctx: Context): Type = {
 if((sym ne ctx.definitions.ScalaPredefModule.moduleClass) && !(sym is Flags.Package) && !(sym.isAnonymousClass))
    tp match {
      case t: ClassInfo =>
        def generateSpecializations(remainingTParams: List[Name], remainingBounds: List[TypeBounds])
                                   (instantiations: List[Type], names: List[String], poly: PolyType)(implicit ctx: Context): List[Symbol] = {
          if (remainingTParams.nonEmpty) {
            val bounds = remainingBounds.head
            (for (tpe <- {
              primitiveTypes
                .filter { tpe =>
                bounds.contains(tpe)
              }
            }) yield {
              generateSpecializations(remainingTParams.tail, remainingBounds.tail)(tpe :: instantiations, specialisedTypeToSuffix(ctx)(tpe) :: names, poly)
            }).flatten
          }
          else {
            generateSpecializedSymbols(instantiations.reverse, names.reverse, poly)
          }
        }

        def generateSpecializedSymbols(instantiations: List[Type], names: List[String], poly: PolyType)(implicit ctx: Context): List[Symbol] = {
          val newSym = ctx.newSymbol(sym.owner, (sym.name + names.mkString).toTermName, sym.flags | Flags.Synthetic, poly.instantiate(instantiations.toList))
          val prev = newSymbolMap.getOrElse(sym, (Nil, Nil))
          val newSyms = newSym :: prev._1
          val newInsts = instantiations ::: prev._2
          newSymbolMap.put(sym, (newSyms, newInsts))
          newSyms
        }

        def shouldSpecialize(decl: Symbol)(implicit ctx: Context): Boolean =
          specializationRequests.contains(sym) ||
            (ctx.settings.Yspecialize.value != "" && decl.name.contains(ctx.settings.Yspecialize.value)) ||
            ctx.settings.Yspecialize.value == "all"

        sym.info match {
          case t: ClassInfo =>
            val newDecls = t.decls.flatMap(decl => {
              if (decl eq ctx.definitions.ScalaPredefModule.moduleClass) Nil
              else if (shouldSpecialize(decl)) {
                decl.info.widen match {
                  case poly: PolyType =>
                    if (poly.paramNames.length <= maxTparamsToSpecialize) generateSpecializations(poly.paramNames, poly.paramBounds)(List.empty, List.empty, poly) else Nil
                  case nil =>
                    Nil
                }
              } else Nil
            })
            if (newDecls.isEmpty) t
            else {
              val decls = t.decls.cloneScope
              newDecls.foreach(decls.enter)
              t.derivedClassInfo(decls = decls)
            }
          case nil => Nil
        }
        tp
      case _ =>
        tp
    }
    else tp
  }

  def registerSpecializationRequest(method: Symbols.Symbol)(arguments: List[Type])(implicit ctx: Context) = {
    if(ctx.phaseId > this.treeTransformPhase.id)
      assert(ctx.phaseId <= this.treeTransformPhase.id)
    val prev = specializationRequests.getOrElse(method, List.empty)
    specializationRequests.put(method, arguments :: prev)
  }

  def specializeForAll(sym: Symbols.Symbol)(implicit ctx: Context): List[List[Type]] = {
    registerSpecializationRequest(sym)(primitiveTypes)
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
              specializeForSome(sym)(types.map(tpeTree => //tpeTree.tpe.widen))
                nameToSpecialisedType(ctx)(tpeTree.tpe.asInstanceOf[TermRef].name.toString())))
            case List() => specializeForAll(sym)
          }
        case nil =>
          if(ctx.settings.Yspecialize.value == "all") {println("Yspecialize set to all"); specializeForAll(sym) }
          else Nil
      }
  }

  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    tree.tpe.widen match {

      case poly: PolyType if !(tree.symbol.isPrimaryConstructor
                               || (tree.symbol is Flags.Label)) =>
        val origTParams = tree.tparams.map(_.symbol)
        val origVParams = tree.vparamss.flatten.map(_.symbol)
        println(s"specializing ${tree.symbol} for Tparams: $origTParams")

        def specialize(instantiations: List[Type]): List[Tree] = {
          newSymbolMap.getOrElse(tree.symbol, (Nil, Nil)) match {
            case (newSyms: List[Symbol], _: List[Type]) =>
              newSyms.map{newSym =>
              polyDefDef(newSym.asTerm, { tparams => vparams => {
                assert(tparams.isEmpty)
                new TreeTypeMap(
                  typeMap = _
                    .substDealias(origTParams, instantiations.toList)
                    .subst(origVParams, vparams.flatten.map(_.tpe)),
                  oldOwners = tree.symbol :: Nil,
                  newOwners = newSym :: Nil
                ).transform(tree.rhs)
              }
              })}
            case nil =>
              List()
          }
        }

        shouldSpecializeFor(tree.symbol)
        val specializedMethods: List[Tree] = (for (inst <- newSymbolMap.keys) yield specialize(newSymbolMap(inst)._2)).flatten.toList
        Thicket(tree :: specializedMethods)
      case _ => tree
    }
  }

  override def transformTypeApply(tree: tpd.TypeApply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    val TypeApply(fun,args) = tree
    val name = fun.symbol.name



    tree
  }
/*
  def transformTypeOfTree(tree: Tree)(implicit ctx: Context): Tree = tree

  override def transformIdent(tree: Ident)(implicit ctx: Context, info: TransformerInfo): Tree = transformTypeOfTree(tree)
  override def transformSelect(tree: Select)(implicit ctx: Context, info: TransformerInfo): Tree = transformTypeOfTree(tree)
*/
}
