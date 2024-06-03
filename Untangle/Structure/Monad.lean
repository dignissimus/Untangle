import Untangle.Data.Expression
import Untangle.Data.Diagram
import Untangle.Parsing.Auxiliary
import Untangle.Tactic.Auxiliary

open Lean Meta Server Expr Diagram

namespace Monad

mutual
  partial def parseHom (e : Expr) : Option (Expr × Expr) :=
    match getAppFnArgs? e with
      | some (`Quiver.Hom, #[_, _, X, Y]) => return (X, Y)
      | _ => fail

  partial def parseMorphismComposition (e: Expr) : Option (Expression ExpressionType.Morphism) := do
    match getAppFnArgs? e with
      | some (`CategoryTheory.CategoryStruct.comp, #[_, _, X, Y, Z, f, g]) =>
        return Expression.MorphismComposition e
          ( morphismFromTo (← parseMorphism f) (←parseObject X) (←parseObject Y ))
          ( morphismFromTo (← parseMorphism g) (← parseObject Y)  (← parseObject Z))
      | _ => fail


  partial def parseFunctorComposition (e: Expr) : Option (Expression ExpressionType.Functor) := do
    match getAppFnArgs? e with
      | some (`CategoryTheory.Functor.comp, #[_, _, _, _, _, _, F, G]) => Expression.FunctorComposition (← parseFunctor F) (←parseFunctor G)
      | _ => fail

  partial def parseIdentityMorphism(e : Expr) : Option (Expression ExpressionType.Morphism) := do
    match getAppFnArgs? e with
      | some (`CategoryTheory.CategoryStruct.id, #[_, _, X]) => Expression.Morphism e (← parseObject X) (← parseObject X)
      | _ => fail

  -- TODO: Parse the source and destination from the type of the morphism
  partial def parseMorphismName (e : Expr) : Option (Expression ExpressionType.Morphism) :=  return Expression.Morphism e unknown unknown
  partial def parseObjectName (e : Expr) : Option (Expression ExpressionType.Object) :=  return Expression.Object e


  -- TODO
  partial def parseFunctorName (expression : Expr) : Option (Expression ExpressionType.Functor) :=
    match getAppFnArgs? expression with
        | some (`CategoryTheory.Functor.toPrefunctor, #[_, _, C, D]) => do return Expression.Functor expression unknown unknown
        | some (`CategoryTheory.Monad.toFunctor, #[_, _, functor]) => do return Expression.Functor expression unknown unknown
        -- TODO maybe
        | e => Expression.Functor expression unknown unknown
        -- `CategoryTheory.Monad.toFunctor

  partial def parseMorphismLift (e : Expr) : Option (Expression ExpressionType.Morphism) :=
    match getAppFnArgs? e with
      | some (`Prefunctor.map, #[_, _, _, _, functor, X, Y, f]) =>
        return Expression.LiftMap
          (← parseFunctor functor)
          (morphismFromTo (← parseMorphism f) (←parseObject X) (← parseObject Y))
      | _ => fail

  partial def parseObjectLift (e : Expr) : Option (Expression ExpressionType.Object) :=
    match getAppFnArgs? e with
      | some (`Prefunctor.obj, #[_, _, _, _, functor, object]) =>
        return Expression.LiftObject
          (← parseFunctor functor)
          (← parseObject object)
      | _ => fail


  partial def parseNaturalTransformationComponent (e : Expr) : Option (Expression ExpressionType.Morphism) :=
    match getAppFnArgs? e with
      | some (`CategoryTheory.NatTrans.app, #[_, _, _, _, F, G, η, X]) =>
        return Expression.NaturalTransformationComponent
          ( natTransFromTo (← parseNaturalTransformation η) (← parseFunctor F) (←parseFunctor G) )
          (← parseObject X)
          (← parseFunctor F)
          (← parseFunctor G)
      | _ => fail

  partial def parseNaturalTransformation  (e : Expr): Option (Expression ExpressionType.NaturalTransformation) := return Expression.NaturalTransformation e unknown unknown
  partial def parseObject : Expr → Option (Expression ExpressionType.Object) :=
    parseObjectLift
    or parseObjectName

  partial def parseFunctor : Expr → Option (Expression ExpressionType.Functor) :=
    parseFunctorComposition
    or parseFunctorName

  partial def parseMorphism : Expr → Option (Expression ExpressionType.Morphism) :=
    parseMorphismLift
    or parseMorphismComposition
    or parseNaturalTransformationComponent
    or parseIdentityMorphism
    or parseMorphismName

end

def orElse' (f g : X → Y → (RequestM $ Option α)) (x : X) (y : Y) : RequestM $ Option α :=
  do
    if let Option.some _ := (← f x y) then f x y
    else g x y

infixl:65 " or' " => orElse'
macro_rules
  | `(fail) => `(do ← none)

def isMonadMu? (expression : Expr) :=
  match getAppFnArgs? expression with
    | some (`CategoryTheory.Monad.μ, #[_, _, _]) => true
    | _ => false

def isMonadEta? (expression : Expr) :=
  match getAppFnArgs? expression with
    | some (`CategoryTheory.Monad.η, #[_, _, _]) => true
    | _ => false

def monad_left_unit (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent) : RequestM $ Option String :=
  do return do
    if isMonadEta? first.expression && isMonadMu? second.expression then
      return (← fail)
    fail

def monad_right_unit (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent) : RequestM $ Option String :=
  do return do
    if isMonadEta? first.expression && isMonadMu? second.expression then
      return (← fail)
    fail

def monad_assoc (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent) : RequestM $ Option String  :=
  do return do
    if isMonadMu? first.expression && isMonadMu? second.expression then
      return (← fail)
    fail

def naturality  (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent)  : RequestM $ Option String:=
  do
    let prettyFirst : String ← sorry
    let prettySecond : String ← sorry
    return do
      if first.isNaturalTransformation then
        return (← fail)
      if second.isNaturalTransformation then
        return (← fail)
      fail

def GraphicalTactic :=
  monad_left_unit
  or' monad_right_unit
  or' monad_assoc
  or' naturality



-- TODO: Add more rewrite rules
-- TODO: I have access to the Lean Expr so I don't need to build strings
--  I can build tactics as Expr/Syntax and
--   suggest them along the lines of Lean.Meta.Tactic.TryThis.addSuggestion
def generateTactic (goal : Widget.InteractiveGoal) (first : Diagram.DiagramComponent) (second : Diagram.DiagramComponent) : RequestM $ Option (List String) :=
  do
    let (prettyFirst, prettySecond) ← goal.ctx.val.runMetaM {} do
      let md ← goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        return (
          ← toString <$> Lean.Meta.ppExpr first.transformation.label.expression,
          ← toString <$> Lean.Meta.ppExpr second.transformation.label.expression)

    let exp₁ := first.transformation.label.expression
    let exp₂ := second.transformation.label.expression

    let firstIsMonadMu := isMonadMu? exp₁
    let secondIsMonadMu := isMonadMu? exp₂

    let firstIsMonadEta := isMonadEta? exp₁
    let secondIsMonadEta := isMonadEta? exp₂

    -- TODO: Only include the `repeat map_comp` lines when necessary (i.e. check the functor lift count)
    if firstIsMonadEta && secondIsMonadMu then
      let mut tactics := [Repeat $ Rewrite [Symm MapComp]]
      -- TODO: Functor names should be the same
      if first.functorApplications > second.functorApplications then
        tactics := tactics.concat $ Rewrite ["Monad.right_unit"]
      else
        tactics := tactics.concat $ Rewrite ["Monad.left_unit"]
      tactics := tactics.concat $ Repeat (Rewrite [MapComp])
      return tactics
    else if firstIsMonadMu && secondIsMonadMu then
      let mut tactics := [Repeat $ Rewrite [Symm MapComp]]
      if first.functorApplications > second.functorApplications then
        tactics := tactics.concat $ Rewrite ["Monad.assoc"]
      else
        tactics := tactics.concat $ Rewrite ["← Monad.assoc"]
      tactics := tactics.concat $ Repeat (Rewrite [MapComp])
      return tactics
    else if first.isNaturalTransformation then
      return [
        Repeat $ Rewrite [Symm MapComp],
        Rewrite [
          Symm s!"({prettyFirst}).naturality ({prettySecond})",
          "CategoryTheory.Functor.comp_map"
        ],
        Repeat $ Rewrite [MapComp]
      ]
    else if second.isNaturalTransformation then
      return [
        Repeat $ Rewrite [Symm MapComp],
        Rewrite [
          Symm "CategoryTheory.Functor.comp_map",
          s!"({prettySecond}).naturality ({prettyFirst})"
        ],
        Repeat $ Rewrite [MapComp]
      ]
    return .none


-- Note be careful with the following cases
--  μ : (F ⋙ G) ⟶ (F ⋙ G') where μ is not T.map μ'
def expressionAsDiagramInput : Expression α →  List FunctorLike
  | Expression.Object object => [FunctorLike.Object object]
  | Expression.LiftObject functor object => expressionAsDiagramInput object ++ [FunctorLike.Functor (raw functor)]
  | Expression.Functor functor _source _target => [FunctorLike.Functor functor]
  | Expression.FunctorComposition left right => expressionAsDiagramInput left ++ expressionAsDiagramInput right
  | e => panic! s!"As input: {e}"

partial def morphismAsDiagramComponent (location : ℕ) : Expression ExpressionType.Morphism → Option DiagramComponent
  -- TODO: Consider the following case: let f := T.map f'; f ≫ g'
  | Expression.Morphism expr source target =>
    do
    let outputs := expressionAsDiagramInput target
      return {
      inputs := expressionAsDiagramInput source
      transformation := {
        label := TransformationLike.Morphism expr, -- TODO: Read from expr, take MetaM as parameter
        left := 0,
        right := source.countObjectLifts,
        numberOfOutputs := outputs.length
      }
      location
      outputs := outputs
    }
  -- TODO: Might require context? If μ : (T ⋙ T)
  | Expression.LiftMap functor morphism => do (← morphismAsDiagramComponent location morphism).applyFunctor functor
  | Expression.NaturalTransformationComponent transformation object source target =>
    do
      return {
        inputs := (← expressionAsDiagramInput object) ++ (← expressionAsDiagramInput source)
        transformation := {
          label := TransformationLike.NaturalTransformation (raw transformation) -- Read from expr
          left := 1 + object.countObjectLifts
          right := object.countObjectLifts + source.countFunctorApplications
          numberOfOutputs := target.countFunctorApplications
        }
        location
        outputs := (← expressionAsDiagramInput object) ++ (← expressionAsDiagramInput target)
      }

  -- | Expression.MorphismComposition expr f g => return (← morphismAsDiagramComponent $ Expression.Morphism expr (← f.source) (← g.target))
  | e => panic! s!"Unreachable: {e}"

def constructMorphismDiagram (location : ℕ): Expression ExpressionType.Morphism → Option Diagram
  | Expression.MorphismComposition  _ first second => do
    let left ← constructMorphismDiagram location first
    let last ← left.getLast?
    let offset := last.location + 1
    let right ← constructMorphismDiagram offset second
    return left ++ right
  | morphism => do [← morphismAsDiagramComponent location morphism]

def monad : Diagram.GraphicalLanguage where
  parseExpression := parseMorphism
  generateTactic := generateTactic
  isIdentity (e : Expr) : Bool :=
    match getAppFnArgs? e with
      | some (`CategoryTheory.Functor.id, #[_, _]) => true
      | some (`CategoryTheory.CategoryStruct.id, #[_, _, _]) => true
      | _ => false
  renderExpression := constructMorphismDiagram

end Monad
